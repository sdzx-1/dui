{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SP.SP1 where

import qualified Data.IntMap as IntMap
import Data.Sequence
import qualified Data.Sequence as Seq
import SP.Eval
import SP.Gen
import SP.Type
import SP.Util

-----------------------
f1 :: LSP Int Int
f1 =
  arrLSP (+ 0)
    :>>> arrLSPState 0 (\s a -> (s + a, s + a))
    :>>> arrLSP genV
    :>>> (arrLSP (* (-1)) ||| arrLSP id)
    :>>> arrLSP id

genV :: (Int -> Either Int Int)
genV i = if even i then Left i else Right i

reV :: Either Int Int -> Int
reV (Left _) = 0
reV (Right i) = i

ge1 :: MonadFail m => m EvalState
ge1 = do
  (a, _) <- genES (Prelude.replicate 10 1) f1
  run a

-- >>> re1
-- fromList [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[1,-2,3,-4,5,-6,7,-8,9,-10])]
re1 :: IO (IntMap.IntMap [Int])
re1 = hf <$> ge1

-----------------------
