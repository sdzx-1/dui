{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}

module SP.Util where

import qualified Data.IntMap as IntMap
import Data.Sequence (Seq (..))
import GHC.Exts (IsList (toList))
import Optics (imap, (^.))
import SP.Type (ChanState (..), EvalState (EvalState, chans), SP (..), SomeSP, SomeVal (..))
import Unsafe.Coerce (unsafeCoerce)

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

hf :: EvalState -> IntMap.IntMap [v]
hf (EvalState chans _) =
  IntMap.map
    ( \(ChanState chan _) -> chan2v chan
    )
    chans

chan2v :: Seq SomeVal -> [v]
chan2v s = toList $ fmap (\(SomeVal v) -> unsafeCoerce v) s
