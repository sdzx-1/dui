{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module SP.Eval where

import Control.Algebra (Has)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (runState)
import Control.Effect.State (State)
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------

eval :: (Has (State EvalState) sig m, MonadFail m) => m ()
eval = do
  mval <- takeOneSomeSP
  case mval of
    Nothing -> pure ()
    Just sfun -> do
      case sfun of
        ------------------------------------------------------------------------
        BothUp i (o1, o2) -> do
          readVal sfun i $ \(SomeVal val) -> do
            let (va, vb) = unsafeCoerce val
            writeVal (SomeVal va) o1
            writeVal (SomeVal vb) o2
            runningAdd sfun
        ------------------------------------------------------------------------
        BothDownFst si other ti -> do
          len <- getChanLength other
          if len < 1
            then attochSomeSP sfun si
            else do
              readVal sfun si $ \(SomeVal vl) -> do
                SomeVal vr <- onlyReadVal other
                writeVal (SomeVal (vl, vr)) ti
                runningAdd sfun
        ------------------------------------------------------------------------
        BothDownSnd si other ti -> do
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
              let ssp' = SomeSP $ SPWrapper io $ f (unsafeCoerce val)
              runningAdd ssp'
          Put v sp' -> do
            writeVal (SomeVal v) o
            let sp'' = SomeSP (SPWrapper io sp')
            runningAdd sp''
      eval

-- run :: EvalState -> IO (EvalState, ())
run :: MonadFail m => EvalState -> m EvalState
run es = fst <$> runM (runState @EvalState es eval)

runMaybe :: EvalState -> Maybe EvalState
runMaybe es = fst <$> runM (runState @EvalState es eval)
