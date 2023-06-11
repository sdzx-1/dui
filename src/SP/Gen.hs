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

genES' :: (Has (State EvalState :+: Fresh) sig m, MonadFail m) => Int -> LSP i o -> m Int
genES' i (E sp) = do
  i' <- fresh
  assign @EvalState (#chans % at i') (Just initChanState)
  mapM_ runningAdd [SomeSP $ SPWrapper (i, i') sp]
  pure i'
genES' i (lsp :>>> lsps) = do
  i' <- genES' i lsp
  genES' i' lsps
genES' i ((:+++) lsp rsp) = do
  lo <- fresh
  ro <- fresh
  assign @EvalState (#chans % at lo) (Just initChanState)
  assign @EvalState (#chans % at ro) (Just initChanState)
  mapM_ runningAdd [EitherUp i (lo, ro)]

  lo' <- genES' lo lsp
  ro' <- genES' ro rsp

  ko <- fresh
  assign @EvalState (#chans % at ko) (Just initChanState)
  mapM_ runningAdd [EitherDownLeft lo' ko, EitherDownRight ro' ko]

  pure ko
genES' i (lsp :*** rsp) = do
  fsto <- fresh
  sndo <- fresh
  assign @EvalState (#chans % at fsto) (Just initChanState)
  assign @EvalState (#chans % at sndo) (Just initChanState)
  mapM_ runningAdd [BothUp i (fsto, sndo)]

  fsto' <- genES' fsto lsp
  sndo' <- genES' sndo rsp

  ko <- fresh
  assign @EvalState (#chans % at ko) (Just initChanState)
  mapM_ runningAdd [BothDownFst fsto' sndo' ko, BothDownSnd sndo' fsto' ko]

  pure ko

genES :: MonadFail m => [i] -> LSP i o -> m (EvalState, (Int, Int))
genES ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)

genESMaybe :: [i] -> LSP i o -> Maybe (EvalState, (Int, Int))
genESMaybe ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)

runLSP :: [i] -> LSP i o -> Maybe [o]
runLSP ls lsp = do
  (a, (_, i)) <- genESMaybe ls lsp
  EvalState {..} <- runMaybe a
  ChanState {..} <- IntMap.lookup i chans
  pure (fmap (\(SomeVal a) -> unsafeCoerce a) (toList chan))