{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoFieldSelectors #-}

module SP.Eval where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (Fresh, runFresh)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (runState)
import Control.Effect.State (State)
import qualified Control.Effect.State as S
import Control.Monad (forM)
import qualified Data.Map as Map
import GHC.Exts (toList)
import Optics (Ixed (ix), (%), (^?))
import SP.Gen
import SP.SP (SP (..))
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------

eval :: (Has (State EvalState :+: State DynMap :+: Fresh) sig m, MonadFail m) => m ()
eval = do
  mval <- takeOneSomeSP
  case mval of
    Nothing -> pure ()
    Just sfun@(RTSPWrapper index rtsp) -> do
      case rtsp of
        DebugRtSP ouput i o -> do
          es <- S.get @EvalState
          writeVal (SomeVal es) ouput
          readVal sfun i $ \someVal -> do
            writeVal someVal o
            runningAdd sfun
        DirectReadWrite i o -> do
          readVal sfun i $ \someVal -> do
            writeVal someVal o
            runningAdd sfun
        DynSP dysps@(DynSPState i _ _ _) (Action f) -> do
          readVal sfun i $ \(SomeVal a) -> do
            f dysps (unsafeCoerce a)
            runningAdd sfun
        ------------------------------------------------------------------------
        Both i (o1, o2) -> do
          readVal sfun i $ \someVal -> do
            writeVal someVal o1
            writeVal someVal o2
            runningAdd sfun
        ------------------------------------------------------------------------
        LoopEitherDown o1 (leftO, i1) -> do
          readVal sfun o1 $ \(SomeVal val) -> do
            let (eindex, someVal') = case unsafeCoerce val of
                  Left leftVal -> (leftO, SomeVal leftVal)
                  Right rightVal -> (i1, SomeVal (Right rightVal))
            writeVal someVal' eindex
            runningAdd sfun
        ------------------------------------------------------------------------
        TupleUp i (o1, o2) -> do
          readVal sfun i $ \(SomeVal val) -> do
            let (va, vb) = unsafeCoerce val
            writeVal (SomeVal va) o1
            writeVal (SomeVal vb) o2
            runningAdd sfun
        ------------------------------------------------------------------------
        TupleDownFst si other ti -> do
          len <- getChanLength other
          if len < 1
            then attochSomeSP sfun si
            else do
              readVal sfun si $ \(SomeVal vl) -> do
                SomeVal vr <- onlyReadVal other
                writeVal (SomeVal (vl, vr)) ti
                runningAdd sfun
        ------------------------------------------------------------------------
        TupleDownSnd si other ti -> do
          len <- getChanLength other
          if len < 1
            then attochSomeSP sfun si
            else do
              readVal sfun si $ \(SomeVal vr) -> do
                SomeVal vl <- onlyReadVal other
                writeVal (SomeVal (vl, vr)) ti
                runningAdd sfun
        ------------------------------------------------------------------------
        EitherUp i (el, er) -> do
          readVal sfun i $ \(SomeVal val) -> do
            let (eindex, someVal') = case unsafeCoerce val of
                  Left leftVal -> (el, SomeVal leftVal)
                  Right rightVal -> (er, SomeVal rightVal)
            writeVal someVal' eindex
            runningAdd sfun
        ------------------------------------------------------------------------
        EitherDownLeft i o -> do
          readVal sfun i $ \(SomeVal val) -> do
            writeVal (SomeVal (Left val)) o
            runningAdd sfun
        EitherDownRight i o -> do
          readVal sfun i $ \(SomeVal val) -> do
            writeVal (SomeVal (Right val)) o
            runningAdd sfun
        ------------------------------------------------------------------------
        SomeSP (SPWrapper io@(i, o) sp) -> case sp of
          Get f -> do
            readVal sfun i $ \(SomeVal val) -> do
              let ssp' = RTSPWrapper index $ SomeSP $ SPWrapper io $ f (unsafeCoerce val)
              runningAdd ssp'
          Put v sp' -> do
            writeVal (SomeVal v) o
            let sp'' = RTSPWrapper index $ SomeSP (SPWrapper io sp')
            runningAdd sp''
          Return a -> pure a
      eval

genESMaybe :: [i] -> LSP xs i o -> Maybe (EvalState, (DynMap, (Int, GenResult)))
genESMaybe ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runState @DynMap Map.empty $
        runFresh 1 (genES' 0 lsp)

genESAndRun :: [i] -> LSP xs i o -> Maybe (EvalState, (DynMap, (Int, GenResult)))
genESAndRun ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runState @DynMap Map.empty $
        runFresh 1 $ do
          res <- genES' 0 lsp
          eval
          pure res

runLSP :: [i] -> LSP xs i o -> Maybe [o]
runLSP ls lsp = do
  genESArrest lsp
  (es, (_, (_, GenResult _ i _ _ _))) <- genESAndRun ls lsp
  os <- es ^? (#chans % ix i % #chan)
  pure (fmap (\(SomeVal a) -> unsafeCoerce a) (toList os))

runLSPWithOutputs ::
  SomeValsToHList outputs =>
  [i] ->
  LSP outputs i o ->
  Maybe (HList outputs, [o])
runLSPWithOutputs ls lsp = do
  genESArrest lsp
  (es, (_, (_, GenResult outputIndexList i _ _ _))) <- genESAndRun ls lsp
  os <- es ^? (#chans % ix i % #chan)
  let o = fmap (\(SomeVal a) -> unsafeCoerce a) (toList os)
  outputSomeValList <- forM outputIndexList $ \i -> es ^? (#chans % ix i % #chan)
  pure (someValsToHList outputSomeValList, o)