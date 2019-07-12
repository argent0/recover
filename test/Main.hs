module Main where

import Test.DocTest

main :: IO ()
main = doctest ["-v", "src/Data/Recover.hs"]
