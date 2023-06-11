{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module SP.Util where

import Control.Algebra (Has)
import Control.Carrier.State.Strict (State)
import Control.Effect.Optics (assign, modifying, preuse, use)
import qualified Data.IntMap as IntMap
import Data.Sequence (Seq (..), (><))
import qualified Data.Sequence as Seq
import GHC.Exts (IsList (toList))
import Optics (Ixed (ix), (%))
import SP.Type
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad (forM_)

readChan :: SomeSP -> ChanState -> (ChanState, Maybe SomeVal)
readChan ssp cs@ChanState {..} = case chan of
  Empty -> (cs {waitingList = waitingList :|> ssp}, Nothing)
  (v :<| vs) -> (cs {chan = vs}, Just v)

writeChan :: SomeVal -> ChanState -> (ChanState, Maybe SomeSP)
writeChan sv cs@ChanState {..} = case waitingList of
  Empty -> (cs {chan = chan :|> sv}, Nothing)
  (sp :<| sps) ->
    ( cs
        { chan = chan :|> sv,
          waitingList = sps
        },
      Just sp
    )

filterSP :: (a -> Bool) -> SP a a
filterSP p = Get $ \x ->
  if p x
    then Put x (filterSP p)
    else filterSP p

arrSP :: (a -> b) -> SP a b
arrSP f = Get $ \x -> Put (f x) (arrSP f)

arrSPState :: s -> (s -> a -> (s, b)) -> SP a b
arrSPState s f = Get $ \a ->
  let (s', b) = f s a
   in Put b (arrSPState s' f)

allChansValues :: EvalState -> IntMap.IntMap [v]
allChansValues (EvalState chans _) =
  IntMap.map
    ( \(ChanState chan _) -> chan2v chan
    )
    chans

chan2v :: Seq SomeVal -> [v]
chan2v s = toList $ fmap (\(SomeVal v) -> unsafeCoerce v) s

initChanState :: ChanState
initChanState =
  ChanState
    { chan = Seq.empty,
      waitingList = Seq.empty
    }

initEvalState :: [i] -> EvalState
initEvalState ls =
  EvalState
    { chans =
        IntMap.fromList
          [ ( 0,
              ChanState
                { chan = Seq.fromList (map SomeVal ls),
                  waitingList = Seq.empty
                }
            )
          ],
      runningList = Seq.empty
    }

takeOne :: Seq a -> (Maybe a, Seq a)
takeOne Empty = (Nothing, Empty)
takeOne (v :<| res) = (Just v, res)

takeOneSomeSP ::
  (Has (State EvalState) sig m, MonadFail m) => m (Maybe SomeSP)
takeOneSomeSP = do
  runs <- use @EvalState #runningList
  let (v, n) = takeOne runs
  assign @EvalState #runningList n
  pure v

runningAdd ::
  (Has (State EvalState) sig m, MonadFail m) => SomeSP -> m ()
runningAdd ssp = modifying @_ @EvalState #runningList (:|> ssp)

readVal ::
  (Has (State EvalState) sig m, MonadFail m) => SomeSP -> Int -> m (Maybe SomeVal)
readVal ssp i = do
  Just cs <- preuse @EvalState (#chans % ix i)
  let (cs', mv) = readChan ssp cs
  assign @EvalState (#chans % ix i) cs'
  pure mv

writeVal ::
  (Has (State EvalState) sig m, MonadFail m) => SomeVal -> Int -> m ()
writeVal sval o = do
  Just cs <- preuse @EvalState (#chans % ix o)
  let (cs', msp) = writeChan sval cs
  assign @EvalState (#chans % ix o) cs'
  forM_ msp runningAdd

filterLSP :: (a -> Bool) -> LSP a a
filterLSP p = E (filterSP p)

arrLSP :: (a -> b) -> LSP a b
arrLSP f = E (arrSP f)

arrLSPState :: s -> (s -> a -> (s, b)) -> LSP a b
arrLSPState s f = E (arrSPState s f)

(|||) :: LSP i1 o -> LSP i2 o -> LSP (Either i1 i2) o
l ||| r = (l :+++ r) :>>> arrLSP bothC

bothC :: Either a a -> a
bothC (Left a) = a
bothC (Right a) = a
