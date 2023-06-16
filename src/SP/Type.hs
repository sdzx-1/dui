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
import Data.Kind (Constraint, Type)
import Data.Sequence (Seq)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.OldList (intercalate)
import Optics (makeFieldLabels)
import SP.SP

data SPWrapper i o = SPWrapper
  { ioIndex :: (Int, Int),
    sp :: SP i o ()
  }

data SomeVal = forall a. SomeVal a

data SomeSP
  = forall i o. SomeSP (SPWrapper i o)
  | EitherUp Int (Int, Int)
  | EitherDownLeft Int Int
  | EitherDownRight Int Int
  | TupleUp Int (Int, Int)
  | TupleDownFst
      { soureIndex :: Int,
        otherIndex :: Int,
        targeIndex :: Int
      }
  | TupleDownSnd
      { soureIndex :: Int,
        otherIndex :: Int,
        targeIndex :: Int
      }
  | Both Int (Int, Int)
  | LoopEitherDown Int (Int, Int)

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

data HList (xs :: [Type]) where
  (:>) :: [x] -> HList xs -> HList (x ': xs)
  Nil :: HList '[]

type family All (f :: Type -> Constraint) (v :: [Type]) :: Constraint where
  All f '[] = ()
  All f (x ': xs) = (f x, All f xs)

toStringList :: All Show xs => HList xs -> [String]
toStringList Nil = []
toStringList (x :> xs) = show x : toStringList xs

instance All Show xs => Show (HList xs) where
  show xs = "{" ++ intercalate ", " (toStringList xs) ++ "}"

infixr 1 :>

type family Reverse' (a :: [xs]) (b :: [xs]) :: [xs] where
  Reverse' '[] ys = ys
  Reverse' (x ': xs) ys = Reverse' xs (x ': ys)

infixr 2 :++:

type family (:++:) (a :: [xs]) (b :: [xs]) :: [xs] where
  '[] :++: ys = ys
  xs :++: '[] = xs
  xs :++: ys = Reverse' (Reverse' xs '[]) ys

data LSP (outputs :: [Type]) i o where
  E :: (Typeable i, Typeable o) => SP i o () -> LSP '[] i o
  (:>>>) :: LSP xs i o -> LSP ys o p -> LSP (xs :++: ys) i p
  (:+++) :: LSP xs i1 o1 -> LSP ys i2 o2 -> LSP (xs :++: ys) (Either i1 i2) (Either o1 o2)
  (:***) :: LSP xs i1 o1 -> LSP ys i2 o2 -> LSP (xs :++: ys) (i1, i2) (o1, o2)
  LoopEither :: LSP xs (Either i k) (Either o k) -> LSP xs i o
  (:>>+) :: LSP xs i o1 -> LSP ys i o2 -> LSP (xs :++: '[o1] :++: ys) i o2
  -- Dyn :: LSP xs (Either (LSP xs a b) a) b

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
    (LoopEither lsp) -> "[LoopEither " ++ show lsp ++ "]"
    (a :>>+ b) -> "((" ++ show a ++ ") :>+ (" ++ show b ++ "))"