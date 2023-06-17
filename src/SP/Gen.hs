{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Gen where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (fresh, runFresh)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (State, runState)
import Control.Effect.Fresh (Fresh)
import Control.Monad (forM)
import GHC.Exts (IsList (toList))
import Optics (Ixed (ix), (%), (^?))
import SP.Eval
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

genES' :: (Has (State EvalState :+: Fresh) sig m, MonadFail m) => Int -> LSP xs i o -> m ([Int], Int)
genES' i (E sp) = do
  i' <- newCSIndex
  index <- fresh
  mapM_
    runningAdd
    [ RTSPWrapper index $
        SomeSP $
          SPWrapper (i, i') sp
    ]
  pure ([], i')
genES' i (lsp :>>> lsps) = do
  (ots1, i') <- genES' i lsp
  (ots2, i'') <- genES' i' lsps
  pure (ots1 ++ ots2, i'')
genES' i ((:+++) lsp rsp) = do
  lo <- newCSIndex
  ro <- newCSIndex
  index <- fresh
  mapM_ runningAdd [RTSPWrapper index $ EitherUp i (lo, ro)]
  (lots, lo') <- genES' lo lsp
  (rots, ro') <- genES' ro rsp
  ko <- newCSIndex
  index1 <- fresh
  index2 <- fresh
  mapM_
    runningAdd
    [ RTSPWrapper index1 $ EitherDownLeft lo' ko,
      RTSPWrapper index2 $ EitherDownRight ro' ko
    ]
  pure (lots ++ rots, ko)
genES' i (LoopEither lsp) = do
  i1 <- newCSIndex
  index <- fresh
  mapM_ runningAdd [RTSPWrapper index $ EitherDownLeft i i1]
  (ots, o1) <- genES' i1 lsp
  leftO <- newCSIndex
  index1 <- fresh
  mapM_
    runningAdd
    [ RTSPWrapper index1 $
        LoopEitherDown o1 (leftO, i1)
    ]
  pure (ots, leftO)
genES' i (lsp :*** rsp) = do
  fsto <- newCSIndex
  sndo <- newCSIndex
  index <- fresh
  mapM_ runningAdd [RTSPWrapper index $ TupleUp i (fsto, sndo)]
  (fots, fsto') <- genES' fsto lsp
  (sots, sndo') <- genES' sndo rsp
  ko <- newCSIndex
  index1 <- fresh
  index2 <- fresh
  mapM_
    runningAdd
    [ RTSPWrapper index1 $ TupleDownFst fsto' sndo' ko,
      RTSPWrapper index2 $ TupleDownSnd sndo' fsto' ko
    ]
  pure (fots ++ sots, ko)
genES' i (lsp :>>+ rsp) = do
  fsto <- newCSIndex
  sndo <- newCSIndex
  index <- fresh
  mapM_ runningAdd [RTSPWrapper index $ Both i (fsto, sndo)]
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
  es <- runMaybe a
  os <- es ^? (#chans % ix i % #chan)
  pure (fmap (\(SomeVal a) -> unsafeCoerce a) (toList os))

runLSPWithOutputs ::
  SomeValsToHList outputs =>
  [i] ->
  LSP outputs i o ->
  Maybe (HList outputs, [o])
runLSPWithOutputs ls lsp = do
  (a, (_, (outputIndexList, i))) <- genESMaybe ls lsp
  es <- runMaybe a
  os <- es ^? (#chans % ix i % #chan)
  let o = fmap (\(SomeVal a) -> unsafeCoerce a) (toList os)
  outputSomeValList <- forM outputIndexList $ \i -> es ^? (#chans % ix i % #chan)
  pure (someValsToHList outputSomeValList, o)