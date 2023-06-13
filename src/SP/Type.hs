{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module SP.Type where

import Data.IntMap (IntMap)
import Data.Kind (Type)
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

type family Reverse' (a :: [xs]) (b :: [xs]) :: [xs] where
  Reverse' '[] ys = ys
  Reverse' (x ': xs) ys = Reverse' xs (x ': ys)

infixl 2 :++:

type family (:++:) (a :: [xs]) (b :: [xs]) :: [xs] where
  xs :++: ys = Reverse' (Reverse' xs '[]) ys

data LSP (outputs :: [Type]) i o where
  E :: SP i o -> LSP '[] i o
  (:>>>) :: LSP xs i o -> LSP ys o p -> LSP (xs :++: ys) i p
  (:+++) :: LSP xs i1 o1 -> LSP ys i2 o2 -> LSP (xs :++: ys) (Either i1 i2) (Either o1 o2)
  (:***) :: LSP xs i1 o1 -> LSP ys i2 o2 -> LSP (xs :++: ys) (i1, i2) (o1, o2)
  (:>>+) :: LSP xs i o1 -> LSP ys i o2 -> LSP (xs :++: '[o1] :++: ys) i o2

infixr 1 :>>>

infixr 3 :***

infixr 3 :>>+

infixr 2 :+++

instance Show (LSP xs i o) where
  show = \case
    E _ -> "*"
    (a :>>> b) -> show a ++ " -> " ++ show b
    (a :+++ b) -> "((" ++ show a ++ ") +++ (" ++ show b ++ "))"
    (a :*** b) -> "((" ++ show a ++ ") *** (" ++ show b ++ "))"
    (a :>>+ b) -> "((" ++ show a ++ ") :>+ (" ++ show b ++ "))"