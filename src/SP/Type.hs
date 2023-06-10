{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE DeriveGeneric #-}

module SP.Type where

import Data.IntMap (IntMap)
import Data.Sequence (Seq)
import Optics (makeFieldLabels)
import GHC.Generics (Generic)

data SP i o
  = Get (i -> SP i o)
  | Put o (SP i o)

data SPWrapper i o = SPWrapper
  { ioIndex :: (Int, Int),
    sp :: SP i o
  }

data SomeVal = forall a. SomeVal a

data SomeSP
  = forall i o. SomeSP (SPWrapper i o)
  | EitherUp Int (Int, Int)
  | EitherDownLeft Int Int
  | EitherDownRight Int  Int

data ChanState = ChanState
  { chan :: Seq SomeVal,
    waitingList :: Seq SomeSP
  }
  deriving (Generic)

type RunningList = Seq SomeSP

data EvalState = EvalState
  { chans :: IntMap ChanState,
    runningList :: RunningList
  }
  deriving (Generic)

makeFieldLabels ''ChanState
makeFieldLabels ''EvalState

data LSP i o where
  E :: SP i o -> LSP i o
  (:>>>) :: LSP i o -> LSP o p -> LSP i p

infixr 4 :>>>