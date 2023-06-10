{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SP2 where

import qualified Data.IntMap as IntMap
import Data.Sequence
import qualified Data.Sequence as Seq
import SP

infixr 4 :>>>

data LSP i o where
  E :: SP i o -> LSP i o
  (:>>>) :: LSP i o -> LSP o p -> LSP i p
  ----------------------------------------------------
  (:+++) :: LSP i1 o1 -> LSP i2 o2 -> LSP (Either o1 o2) o -> LSP (Either i1 i2) o

-- (:|||) :: LSP i1 o -> LSP i2 o -> LSP o p -> LSP (Either i1 i2) p
----------------------------------------------------
-- (:***) :: LSP i1 o1 -> LSP i2 o2 -> LSP (o1, o2) o -> LSP (i1, i2) o
-- (:&&&) :: LSP i o1 -> LSP i o2 -> LSP (o1, o2) o -> LSP i o
data Index
  = I Int
  | EI Int Int -- a.(Either i1 i2) -> (b. , c.)
  | L Int
  | R Int