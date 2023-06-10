{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module SP.Eval where

import Control.Algebra (Has)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (runState)
import Control.Effect.Optics
import Control.Effect.Optics.Indexed
import Control.Effect.State (State)
import Data.Functor.Identity (Identity)
import Data.IntMap (IntMap)
import Data.Sequence (Seq (Empty, (:<|), (:|>)), (><))
import qualified Data.Sequence as Seq
import Optics (At (at), Ixed (ix), (%))
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------

initChanState :: ChanState
initChanState =
  ChanState
    { chan = Seq.empty,
      waitingList = Seq.empty
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
  (Has (State EvalState) sig m, MonadFail m) => [SomeSP] -> m ()
runningAdd somesps = modifying @_ @EvalState #runningList (>< Seq.fromList somesps)

readVal ::
  (Has (State EvalState) sig m, MonadFail m) => SomeSP -> Int -> m (Maybe SomeVal)
readVal ssp i = do
  Just cs <- preuse @EvalState (#chans % ix i)
  let (cs', mv) = readChan ssp cs
  assign @EvalState (#chans % ix i) cs'
  pure mv

writeVal ::
  (Has (State EvalState) sig m, MonadFail m) => SomeVal -> Int -> m (Maybe SomeSP)
writeVal sval o = do
  Just cs <- preuse @EvalState (#chans % ix o)
  let (cs', msp) = writeChan sval cs
  assign @EvalState (#chans % ix o) cs'
  pure msp

eval :: (Has (State EvalState) sig m, MonadFail m) => m ()
eval = do
  mval <- takeOneSomeSP
  case mval of
    Nothing -> pure ()
    Just sfun -> do
      case sfun of
        EitherUp i (el, er) -> do
          mv <- readVal sfun i
          case mv of
            Nothing -> pure ()
            Just (SomeVal val) -> do
              let (eindex, someVal') = case unsafeCoerce val of
                    Left leftVal -> (el, SomeVal leftVal)
                    Right rightVal -> (er, SomeVal rightVal)
              msp <- writeVal someVal' eindex
              case msp of
                Nothing -> runningAdd [sfun]
                Just nsp -> runningAdd [nsp, sfun]
        ------------------------------------------------------------------------
        EitherDownLeft i o -> do
          mv <- readVal sfun i
          case mv of
            Nothing -> pure ()
            Just (SomeVal val) -> do
              msp <- writeVal (SomeVal (Left val)) o
              case msp of
                Nothing -> runningAdd [sfun]
                Just nsp -> runningAdd [nsp, sfun]
        EitherDownRight i o -> do
          mv <- readVal sfun i
          case mv of
            Nothing -> pure ()
            Just (SomeVal val) -> do
              msp <- writeVal (SomeVal (Right val)) o
              case msp of
                Nothing -> runningAdd [sfun]
                Just nsp -> runningAdd [nsp, sfun]
        ------------------------------------------------------------------------
        SomeSP (SPWrapper io@(i, o) sp) -> case sp of
          Get f -> do
            mv <- readVal sfun i
            case mv of
              Nothing -> pure ()
              Just (SomeVal val) -> do
                let ssp' = SomeSP $ SPWrapper io $ f (unsafeCoerce val)
                runningAdd [ssp']
          Put v sp' -> do
            msp <- writeVal (SomeVal v) o
            let sp'' = SomeSP (SPWrapper io sp')
            case msp of
              Nothing -> runningAdd [sp'']
              Just ksp -> runningAdd [ksp, sp'']
      eval

-- run :: EvalState -> IO (EvalState, ())
run :: MonadFail m => EvalState -> m EvalState
run es = fst <$> runM (runState @EvalState es eval)
