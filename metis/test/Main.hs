module Main (main) where

import qualified Test.Anf
import qualified Test.Compile
import qualified Test.CoreToAsm
import qualified Test.CoreToAsmNew
import Test.Hspec (hspec)
import qualified Test.InstSelection
import qualified Test.Liveness
import qualified Test.LivenessNew
import qualified Test.RegisterAllocation
import qualified Test.SSA
import qualified Test.SimplifyAsm

main :: IO ()
main =
  hspec $ do
    Test.Anf.spec
    Test.Compile.spec
    Test.CoreToAsm.spec
    Test.CoreToAsmNew.spec
    Test.InstSelection.spec
    Test.Liveness.spec
    Test.LivenessNew.spec
    Test.RegisterAllocation.spec
    Test.SSA.spec
    Test.SimplifyAsm.spec
