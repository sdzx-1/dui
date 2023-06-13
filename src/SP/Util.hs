{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Util where

import Control.Algebra (Has, (:+:))
import Control.Carrier.State.Strict (State)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Optics (assign, modifying, preuse, use)
import qualified Data.IntMap as IntMap
import Data.Kind (Type)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import GHC.Exts (IsList (toList))
import Optics (At (at), Ixed (ix), (%))
import SP.Type
import Unsafe.Coerce (unsafeCoerce)

readChan :: SomeSP -> ChanState -> (ChanState, Maybe SomeVal)
readChan ssp cs@ChanState {..} = case chan of
  Empty -> (cs {waitingList = waitingList :|> ssp}, Nothing)
  (v :<| vs) -> (cs {chan = vs}, Just v)

readChan' :: ChanState -> (ChanState, Maybe SomeVal)
readChan' cs@ChanState {..} = case chan of
  Empty -> (cs, Nothing)
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

newCSIndex ::
  (Has (State EvalState :+: Fresh) sig m) => m Int
newCSIndex = do
  i <- fresh
  assign @EvalState (#chans % at i) (Just initChanState)
  pure i

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

getChanLength ::
  (Has (State EvalState) sig m, MonadFail m) => Int -> m Int
getChanLength i = do
  Just vs <- preuse @EvalState (#chans % ix i % #chan)
  pure $ Seq.length vs

onlyReadVal ::
  (Has (State EvalState) sig m, MonadFail m) => Int -> m SomeVal
onlyReadVal i = do
  Just cs <- preuse @EvalState (#chans % ix i)
  let (cs', Just mv) = readChan' cs
  assign @EvalState (#chans % ix i) cs'
  pure mv

attochSomeSP ::
  (Has (State EvalState) sig m, MonadFail m) => SomeSP -> Int -> m ()
attochSomeSP ssp i = do
  modifying @_ @EvalState (#chans % ix i % #waitingList) (:|> ssp)

readVal ::
  (Has (State EvalState) sig m, MonadFail m) => SomeSP -> Int -> (SomeVal -> m ()) -> m ()
readVal ssp i handler = do
  Just cs <- preuse @EvalState (#chans % ix i)
  let (cs', mv) = readChan ssp cs
  assign @EvalState (#chans % ix i) cs'
  mapM_ handler mv

writeVal ::
  (Has (State EvalState) sig m, MonadFail m) => SomeVal -> Int -> m ()
writeVal sval o = do
  Just cs <- preuse @EvalState (#chans % ix o)
  let (cs', msp) = writeChan sval cs
  assign @EvalState (#chans % ix o) cs'
  mapM_ runningAdd msp

filterLSP :: (a -> Bool) -> LSP '[] a a
filterLSP p = E (filterSP p)

arrLSP :: (a -> b) -> LSP '[] a b
arrLSP f = E (arrSP f)

arrLSPState :: s -> (s -> a -> (s, b)) -> LSP '[] a b
arrLSPState s f = E (arrSPState s f)

infixr 3 &&&

infixr 2 |||

(|||) :: LSP xs i1 o -> LSP ys i2 o -> LSP (xs :++: ys :++: '[]) (Either i1 i2) o
l ||| r = (l :+++ r) :>>> arrLSP bothC

(&&&) :: LSP xs i o1 -> LSP ys i o2 -> LSP (xs :++: ys) i (o1, o2)
f &&& s = arrLSP (\x -> (x, x)) :>>> (f :*** s)

bothC :: Either a a -> a
bothC (Left a) = a
bothC (Right a) = a

class SomeValsToHList (xs :: [Type]) where
  someValsToHList :: [Seq SomeVal] -> HList xs

instance SomeValsToHList '[] where
  someValsToHList [] = Nil
  someValsToHList _ = error "length error"

instance (SomeValsToHList xs) => SomeValsToHList (x ': xs) where
  someValsToHList (x : xs) = map (\(SomeVal a) -> unsafeCoerce a) (toList x) :> someValsToHList xs
  someValsToHList [] = error "length error"