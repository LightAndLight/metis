module Main (main) where

import qualified Test.CoreToAsm
import Test.Hspec (hspec)

main :: IO ()
main =
  hspec $ do
    Test.CoreToAsm.spec
