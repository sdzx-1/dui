{-# LANGUAGE FlexibleInstances #-}
module Test.SP.Eval where

import Data.Function ((&))
import Data.List (foldl')
import SP.Gen
import SP.Type
import SP.Util
import Test.QuickCheck (Arbitrary (arbitrary))

data TestEnv = TestEnv [Int] [Int -> Int]

instance Show TestEnv where
  show (TestEnv ls _) = "TestEnv " ++ show ls ++ " , [function]"

instance Arbitrary TestEnv where
  arbitrary = do
    i <- arbitrary
    TestEnv i <$> arbitrary

dirEvalTestEnv :: TestEnv -> [Int]
dirEvalTestEnv (TestEnv ls fs) = map (\x -> foldl' (&) x fs) ls

creatFunLSP :: [a -> a] -> LSP a a
creatFunLSP = foldr ((:>>>) . arrLSP) (arrLSP id)

lspEvalTestEnv :: TestEnv -> Maybe [Int]
lspEvalTestEnv (TestEnv ls fs) = runLSP ls (creatFunLSP fs)

prop_TestEnv :: TestEnv -> Bool
prop_TestEnv testEnv = lspEvalTestEnv testEnv == Just (dirEvalTestEnv testEnv)

--------------------------
bra :: Int -> Either Int Int
bra i = if odd i then Left i else Right i

fun1 :: (Int -> Int) -> (Int -> Int) -> LSP Int Int
fun1 f1 f2 = arrLSP bra :>>> (arrLSP f1 ||| arrLSP f2)

instance Show (Int -> Int) where
  show _ = "function :: Int -> Int"

prop_fun1 :: (Int -> Int) -> (Int -> Int) -> [Int] -> Bool
prop_fun1 f1 f2 ls =
  runLSP ls (fun1 f1 f2)
    == Just (map (\x -> if odd x then f1 x else f2 x) ls)