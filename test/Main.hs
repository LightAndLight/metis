module Main (main) where

import qualified Test.Anf
import qualified Test.CoreToAsm
import Test.Hspec (hspec)
import qualified Test.Liveness

main :: IO ()
main =
  hspec $ do
    Test.Anf.spec
    Test.CoreToAsm.spec
    Test.Liveness.spec
