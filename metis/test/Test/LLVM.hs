module Test.LLVM (spec) where

import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO
import LLVM.IRBuilder.Module (buildModule)
import LLVM.Pretty (ppllvm)
import Metis.Compile (ProgramResult (..), Stdin (..), Stdout (..), runProgram)
import Metis.LLVM (llvmTypeDicts)
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import Test.Hspec (Spec, describe, expectationFailure, it)

shouldCompile :: Lazy.Text -> IO ()
shouldCompile moduleText =
  withSystemTempFile "testCompile.ll" $ \path handle -> do
    Data.Text.Lazy.IO.hPutStrLn handle moduleText
    hClose handle
    result <- runProgram "llc" [path, "--filetype=null", "-o", "/dev/null"] NoStdin IgnoreStdout
    case result of
      Left err ->
        expectationFailure $ show err
      Right ProgramResult{stdout = ()} ->
        pure ()

spec :: Spec
spec =
  describe "Test.LLVM" $ do
    describe "llvmTypeDicts" $ do
      it "compiles" $ do
        let module_ = buildModule "test" llvmTypeDicts
        let moduleText = ppllvm module_
        shouldCompile moduleText