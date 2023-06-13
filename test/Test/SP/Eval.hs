{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

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

creatFunLSP :: [a -> a] -> LSP '[] a a
creatFunLSP = foldr ((:>>>) . arrLSP) (arrLSP id)

lspEvalTestEnv :: TestEnv -> Maybe [Int]
lspEvalTestEnv (TestEnv ls fs) = runLSP ls (creatFunLSP fs)

prop_TestEnv :: TestEnv -> Bool
prop_TestEnv testEnv = lspEvalTestEnv testEnv == Just (dirEvalTestEnv testEnv)

--------------------------

instance Show (a -> b) where
  show _ = "function :: a -> b"

bra :: Int -> Either Int Int
bra i = if odd i then Left i else Right i

fun1 :: (Int -> Int) -> (Int -> Int) -> LSP '[] Int Int
fun1 f1 f2 = arrLSP bra :>>> (arrLSP f1 ||| arrLSP f2)

prop_fun1 :: (Int -> Int) -> (Int -> Int) -> [Int] -> Bool
prop_fun1 f1 f2 ls =
  runLSP ls (fun1 f1 f2)
    == Just (map (\x -> if odd x then f1 x else f2 x) ls)

--------------------------
fun2 :: (Int -> Bool) -> LSP '[] Int Int
fun2 = filterLSP

prop_fun2 :: (Int -> Bool) -> [Int] -> Bool
prop_fun2 f ls = runLSP ls (fun2 f) == Just (filter f ls)

prop_fun3 :: (Int -> Bool) -> (Int -> Bool) -> [Int] -> Bool
prop_fun3 fstf sndf ls =
  runLSP ls (filterLSP fstf &&& filterLSP sndf)
    == Just (zip (filter fstf ls) (filter sndf ls))

copyVal = idLSP :>>+ idLSP

fun3 f1 f2 f3 =
  arrLSP f1
    :>>> copyVal
    :>>> arrLSP f2
    :>>> copyVal
    :>>> arrLSP f3

prop_fun4 :: (Int -> Int) -> (Int -> Int) -> (Int -> Int) -> [Int] -> Bool
prop_fun4 f1 f2 f3 ls =
  let Just (a :> b :> Nil, c) = runLSPWithOutputs ls (fun3 f1 f2 f3)
   in a == map f1 ls
        && b == map (f2 . f1) ls
        && c == map (f3 . f2 . f1) ls
