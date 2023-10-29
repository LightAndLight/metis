module Main (main) where

import qualified Test.Compile
import Test.Hspec (hspec)
import qualified Test.LLVM

main :: IO ()
main =
  hspec $ do
    Test.Compile.spec
    Test.LLVM.spec
