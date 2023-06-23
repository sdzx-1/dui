{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module SP.BaseType where

import Data.Sequence (Seq)
import GHC.Generics (Generic)
import Optics (makeFieldLabels)

newtype ChanIndex = ChanIndex Int
  deriving (Show, Eq, Ord)

chanIndexToInt :: ChanIndex -> Int
chanIndexToInt (ChanIndex i) = i

intToChanIndex :: Int -> ChanIndex
intToChanIndex = ChanIndex

data Rect = Rect
  { rectX :: Double,
    rectY :: Double,
    rectW :: Double,
    rectH :: Double
  }
  deriving (Generic, Show)

data Point = Point
  { pointX :: Double,
    pointY :: Double
  }
  deriving (Generic, Show)

newtype Event = Event LocalEvent
  deriving (Show)

data Picture = Picture Rect LoclPicture
  deriving (Show)

data LocalEvent
  = LClick Point
  | Drag Double Double
  deriving (Show)

data LoclPicture
  = LRect Rect
  | LPictures [Picture]
  | LString String
  deriving (Show)

data ContainerState = ContainerState
  { containerRect :: Rect,
    focus :: Maybe (ChanIndex, Picture),
    picturesList :: Seq (ChanIndex, Picture)
  }
  deriving (Generic, Show)

makeFieldLabels ''Point
makeFieldLabels ''Rect
makeFieldLabels ''ContainerState