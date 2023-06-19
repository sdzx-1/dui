{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module SP.Type where

import Control.Algebra (Has, (:+:))
import Control.Carrier.State.Strict (State)
import Control.Effect.Fresh (Fresh)
import Data.IntMap (IntMap)
import Data.Kind (Constraint, Type)
import Data.Map (Map)
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

data RTSPWrapper = RTSPWrapper Int RTSP

extraIndex :: RTSPWrapper -> Int
extraIndex (RTSPWrapper i _) = i

data RTSP where
  SomeSP :: (SPWrapper i o) -> RTSP
  EitherUp :: Int -> (Int, Int) -> RTSP
  EitherDownLeft :: Int -> Int -> RTSP
  EitherDownRight :: Int -> Int -> RTSP
  TupleUp :: Int -> (Int, Int) -> RTSP
  TupleDownFst ::
    { soureIndex :: Int,
      otherIndex :: Int,
      targeIndex :: Int
    } ->
    RTSP
  TupleDownSnd ::
    { soureIndex :: Int,
      otherIndex :: Int,
      targeIndex :: Int
    } ->
    RTSP
  Both :: Int -> (Int, Int) -> RTSP
  LoopEitherDown :: Int -> (Int, Int) -> RTSP
  DynSP :: DynSPState -> Action -> RTSP
  DirectReadWrite :: Int -> Int -> RTSP

newtype Action = Action
  { runAction ::
      forall a b m sig.
      ( MonadFail m,
        Has (State EvalState :+: State DynMap :+: Fresh) sig m
      ) =>
      DynSPState ->
      Either (LSP '[] a b) a ->
      m ()
  }

data ChanState = ChanState
  { chan :: Seq SomeVal,
    waitingList :: Seq RTSPWrapper
  }
  deriving (Generic)

type RunningList = Seq RTSPWrapper

data EvalState = EvalState
  { chans :: IntMap ChanState,
    runningList :: RunningList
  }
  deriving (Generic)

data HList (xs :: [Type]) where
  (:>) :: [x] -> HList xs -> HList (x ': xs)
  Nil :: HList '[]

class HListLength (x :: [Type]) where
  hListLength :: Int

instance HListLength '[] where
  hListLength = 0

instance HListLength xs => HListLength (x ': xs) where
  hListLength = 1 + hListLength @xs

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
  (:+++) ::
    (Typeable i1, Typeable i2, Typeable o1, Typeable o2) =>
    LSP xs i1 o1 ->
    LSP ys i2 o2 ->
    LSP (xs :++: ys) (Either i1 i2) (Either o1 o2)
  (:***) ::
    (Typeable i1, Typeable i2, Typeable o1, Typeable o2) =>
    LSP xs i1 o1 ->
    LSP ys i2 o2 ->
    LSP (xs :++: ys) (i1, i2) (o1, o2)
  LoopEither ::
    ( Typeable i,
      Typeable k,
      Typeable o
    ) =>
    LSP xs (Either i k) (Either o k) ->
    LSP xs i o
  (:>>+) ::
    (Typeable i) =>
    LSP xs i o1 ->
    LSP ys i o2 ->
    LSP (xs :++: '[o1] :++: ys) i o2
  Dyn :: HListLength xs => LSP xs (Either (LSP xs a b) a) b

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
    Dyn -> " Dyn "

newtype DynSpecialNum = DynSpecialNum Int deriving (Show, Eq, Ord)

data DynSPState = DynSPState
  { upstreamChan :: Int,
    downstreamChan :: Int,
    dynSpecialNum :: DynSpecialNum,
    debugOutputs :: [Int]
  }
  deriving (Generic)

data SomeLSP = forall a b. SomeLSP (LSP '[] a b)

type DynMap = Map DynSpecialNum LSPGenState

data LSPGenState = LspGenState
  { lspSource :: SomeLSP,
    startChanIndex :: Int,
    allRTSPIndexs :: [Int],
    allChanIndexs :: [Int],
    allDynSpecialNum :: [DynSpecialNum]
  }
  deriving (Generic)

makeFieldLabels ''ChanState
makeFieldLabels ''EvalState
makeFieldLabels ''LSPGenState
makeFieldLabels ''DynSPState
