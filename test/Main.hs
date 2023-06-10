module Main (main) where

import Test.SP.Eval
import Test.QuickCheck (quickCheck)

main :: IO ()
main = do 
    quickCheck prop_TestEnv
