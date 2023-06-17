{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Gen where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (runFresh)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (State, runState)
import Control.Effect.Fresh (Fresh)
import Control.Monad (forM)
import Data.List (sort)
import GHC.Exts (IsList (toList))
import Optics (Ixed (ix), (%), (^.), (^?))
import SP.Eval
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

data GenResult = GenResult
  { -- | all (:>>+) First Branch ChanState index collects
    allBFCI :: [Int],
    -- | LSP output ChanState index
    lspOI :: Int,
    -- | all RTSP index list
    allRTSPI :: [Int]
  }

genES' ::
  ( Has (State EvalState :+: Fresh) sig m,
    MonadFail m
  ) =>
  Int ->
  LSP xs i o ->
  m GenResult
genES' i (E sp) = do
  i' <- newCSIndex
  index <- addRTSP $ SomeSP $ SPWrapper (i, i') sp
  pure $ GenResult [] i' [index]
genES' i (lsp :>>> lsps) = do
  GenResult ots1 i' i1s <- genES' i lsp
  GenResult ots2 i'' i2s <- genES' i' lsps
  pure $ GenResult (ots1 ++ ots2) i'' (i1s ++ i2s)
genES' i ((:+++) lsp rsp) = do
  lo <- newCSIndex
  ro <- newCSIndex
  ie <- addRTSP $ EitherUp i (lo, ro)
  GenResult lots lo' i1s <- genES' lo lsp
  GenResult rots ro' i2s <- genES' ro rsp
  ko <- newCSIndex
  ies <-
    addRTSPList
      [ EitherDownLeft lo' ko,
        EitherDownRight ro' ko
      ]
  pure $ GenResult (lots ++ rots) ko (i1s ++ i2s ++ [ie] ++ ies)
genES' i (LoopEither lsp) = do
  i1 <- newCSIndex
  il <- addRTSP $ EitherDownLeft i i1
  GenResult ots o1 is <- genES' i1 lsp
  leftO <- newCSIndex
  ill <- addRTSP $ LoopEitherDown o1 (leftO, i1)
  pure $ GenResult ots leftO (is ++ [il, ill])
genES' i (lsp :*** rsp) = do
  fsto <- newCSIndex
  sndo <- newCSIndex
  it <- addRTSP $ TupleUp i (fsto, sndo)
  GenResult fots fsto' i1s <- genES' fsto lsp
  GenResult sots sndo' i2s <- genES' sndo rsp
  ko <- newCSIndex
  its <-
    addRTSPList
      [ TupleDownFst fsto' sndo' ko,
        TupleDownSnd sndo' fsto' ko
      ]
  pure $ GenResult (fots ++ sots) ko (i1s ++ i2s ++ [it] ++ its)
genES' i (lsp :>>+ rsp) = do
  fsto <- newCSIndex
  sndo <- newCSIndex
  ib <- addRTSP $ Both i (fsto, sndo)
  GenResult fots fsto' i1s <- genES' fsto lsp
  GenResult sots sndo' i2s <- genES' sndo rsp
  pure $ GenResult (fots ++ [fsto'] ++ sots) sndo' (i1s ++ i2s ++ [ib])

genES :: MonadFail m => [i] -> LSP xs i o -> m (EvalState, (Int, GenResult))
genES ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)

genESArrest :: MonadFail m => LSP xs i o -> m ()
genESArrest lsp = do
  (es, (_, GenResult _ _ ls)) <- genES [] lsp
  let chans = map extraIndex $ toList $ es ^. #runningList
  if sort chans == sort ls
    then pure ()
    else error $ "generate lsp to EvalState error: " ++ show (chans, ls)

genESMaybe :: [i] -> LSP xs i o -> Maybe (EvalState, (Int, GenResult))
genESMaybe ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' 0 lsp)

runLSP :: [i] -> LSP xs i o -> Maybe [o]
runLSP ls lsp = do
  genESArrest lsp
  (a, (_, GenResult _ i _)) <- genESMaybe ls lsp
  es <- runMaybe a
  os <- es ^? (#chans % ix i % #chan)
  pure (fmap (\(SomeVal a) -> unsafeCoerce a) (toList os))

runLSPWithOutputs ::
  SomeValsToHList outputs =>
  [i] ->
  LSP outputs i o ->
  Maybe (HList outputs, [o])
runLSPWithOutputs ls lsp = do
  genESArrest lsp
  (a, (_, GenResult outputIndexList i _)) <- genESMaybe ls lsp
  es <- runMaybe a
  os <- es ^? (#chans % ix i % #chan)
  let o = fmap (\(SomeVal a) -> unsafeCoerce a) (toList os)
  outputSomeValList <- forM outputIndexList $ \i -> es ^? (#chans % ix i % #chan)
  pure (someValsToHList outputSomeValList, o)