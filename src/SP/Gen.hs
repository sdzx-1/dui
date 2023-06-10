{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Gen where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (runFresh)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (State, runState)
import Control.Effect.Fresh (Fresh, fresh)
import Control.Effect.Optics (assign)
import Optics (At (at), (%))
import SP.Type
import SP.Util

genES' :: (Has (State EvalState :+: Fresh) sig m, MonadFail m) => Int -> LSP i o -> m Int
genES' i (E sp) = do
  i' <- fresh
  assign @EvalState (#chans % at i') (Just initChanState)
  runningAdd [SomeSP $ SPWrapper (i, i') sp]
  pure i'
genES' i (lsp :>>> lsps) = do
  i' <- genES' i lsp
  genES' i' lsps
genES' i ((:+++) lsp rsp) = do
  lo <- fresh
  ro <- fresh
  assign @EvalState (#chans % at lo) (Just initChanState)
  assign @EvalState (#chans % at ro) (Just initChanState)
  runningAdd [EitherUp i (lo, ro)]

  lo' <- genES' lo lsp
  ro' <- genES' ro rsp

  ko <- fresh
  assign @EvalState (#chans % at ko) (Just initChanState)
  runningAdd [EitherDownLeft lo' ko, EitherDownRight ro' ko]

  pure ko

genES :: MonadFail m => [i] -> LSP i o -> m (EvalState, (Int, Int))
genES ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)