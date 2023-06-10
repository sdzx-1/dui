module Test.SP.Eval where

import Data.List (foldl')
import SP.Gen
import SP.Type
import SP.Util
import Test.QuickCheck (Arbitrary (arbitrary))
import Data.Function ((&))

data TestEnv = TestEnv [Int] [Int -> Int]

instance Show TestEnv where
  show (TestEnv ls _) = "TestEnv " ++ show ls  ++ " , [function]"

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
