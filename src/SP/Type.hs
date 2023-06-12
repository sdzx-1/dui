{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module SP.Type where

import Data.IntMap (IntMap)
import Data.Sequence (Seq)
import GHC.Generics (Generic)
import Optics (makeFieldLabels)

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
  | EitherDownRight Int Int
  | BothUp Int (Int, Int)
  | BothDownFst
      { soureIndex :: Int,
        otherIndex :: Int,
        targeIndex :: Int
      }
  | BothDownSnd
      { soureIndex :: Int,
        otherIndex :: Int,
        targeIndex :: Int
      }

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
  (:+++) :: LSP i1 o1 -> LSP i2 o2 -> LSP (Either i1 i2) (Either o1 o2)
  (:***) :: LSP i1 o1 -> LSP i2 o2 -> LSP (i1, i2) (o1, o2)

infixr 1 :>>>
infixr 3 :***
infixr 2 :+++

instance Show (LSP i o) where
  show = \case
    E _ -> "*"
    (a :>>> b) -> show a ++ " -> " ++ show b
    (a :+++ b) -> "((" ++ show a ++ ") +++ (" ++ show b ++ "))"
    (a :*** b) -> "((" ++ show a ++ ") *** (" ++ show b ++ "))"