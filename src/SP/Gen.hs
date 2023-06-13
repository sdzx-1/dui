{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Gen where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (runFresh)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (State, runState)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Optics (assign)
import qualified Data.IntMap as IntMap
import GHC.Exts (IsList (toList))
import Optics (At (at), (%))
import SP.Eval
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

genES' :: (Has (State EvalState :+: Fresh) sig m, MonadFail m) => Int -> LSP xs i o -> m ([Int], Int)
genES' i (E sp) = do
  i' <- fresh
  assign @EvalState (#chans % at i') (Just initChanState)
  mapM_ runningAdd [SomeSP $ SPWrapper (i, i') sp]
  pure ([], i')
genES' i (lsp :>>> lsps) = do
  (ots1, i') <- genES' i lsp
  (ots2, i'') <- genES' i' lsps
  pure (ots1 ++ ots2, i'')
genES' i ((:+++) lsp rsp) = do
  lo <- fresh
  ro <- fresh
  assign @EvalState (#chans % at lo) (Just initChanState)
  assign @EvalState (#chans % at ro) (Just initChanState)
  mapM_ runningAdd [EitherUp i (lo, ro)]
  (lots, lo') <- genES' lo lsp
  (rots, ro') <- genES' ro rsp
  ko <- fresh
  assign @EvalState (#chans % at ko) (Just initChanState)
  mapM_ runningAdd [EitherDownLeft lo' ko, EitherDownRight ro' ko]
  pure (lots ++ rots, ko)
genES' i (lsp :*** rsp) = do
  fsto <- fresh
  sndo <- fresh
  assign @EvalState (#chans % at fsto) (Just initChanState)
  assign @EvalState (#chans % at sndo) (Just initChanState)
  mapM_ runningAdd [BothUp i (fsto, sndo)]
  (fots, fsto') <- genES' fsto lsp
  (sots, sndo') <- genES' sndo rsp
  ko <- fresh
  assign @EvalState (#chans % at ko) (Just initChanState)
  mapM_ runningAdd [BothDownFst fsto' sndo' ko, BothDownSnd sndo' fsto' ko]
  pure (fots ++ sots, ko)
genES' i (lsp :>>+ rsp) = do
  fsto <- fresh
  sndo <- fresh
  assign @EvalState (#chans % at fsto) (Just initChanState)
  assign @EvalState (#chans % at sndo) (Just initChanState)
  mapM_ runningAdd [BothUp i (fsto, sndo)]
  (fots, fsto') <- genES' fsto lsp
  (sots, sndo') <- genES' sndo rsp
  pure (fots ++ [fsto'] ++ sots, sndo')

genES :: MonadFail m => [i] -> LSP xs i o -> m (EvalState, (Int, ([Int], Int)))
genES ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)

genESMaybe :: [i] -> LSP xs i o -> Maybe (EvalState, (Int, ([Int], Int)))
genESMaybe ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)

runLSP :: [i] -> LSP xs i o -> Maybe [o]
runLSP ls lsp = do
  (a, (_, (_, i))) <- genESMaybe ls lsp
  EvalState {..} <- runMaybe a
  ChanState {..} <- IntMap.lookup i chans
  pure (fmap (\(SomeVal a) -> unsafeCoerce a) (toList chan))

runLSPWithOutputs :: [i] -> LSP xs i o -> Maybe [o]
runLSPWithOutputs ls lsp = do
  (a, (_, (_, i))) <- genESMaybe ls lsp
  EvalState {..} <- runMaybe a
  ChanState {..} <- IntMap.lookup i chans
  pure (fmap (\(SomeVal a) -> unsafeCoerce a) (toList chan))