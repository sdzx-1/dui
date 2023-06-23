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
  deriving (Show)

chanIndexToInt :: ChanIndex -> Int
chanIndexToInt (ChanIndex i) = i

intToChanIndex :: Int -> ChanIndex
intToChanIndex = ChanIndex

data Rect = Rect
  { rectW :: Double,
    rectH :: Double,
    rectX :: Double,
    rectY :: Double
  }
  deriving (Generic, Show)

data Point = Point
  { pointX :: Double,
    pointY :: Double
  }
  deriving (Generic, Show)

data Event = Event Rect LocalEvent
  deriving (Show)

data Picture = Picture Rect LoclPicture
  deriving (Show)

newtype LocalEvent
  = Click Point
  deriving (Show)

data LoclPicture
  = LRect Rect
  | LPictures [Picture]
  deriving (Show)

data ContainerState = ContainerState
  { focus :: Maybe (ChanIndex, Picture),
    picturesList :: Seq (ChanIndex, Picture),
    containerRect :: Rect
  }
  deriving (Generic, Show)

makeFieldLabels ''Point
makeFieldLabels ''Rect
makeFieldLabels ''ContainerState