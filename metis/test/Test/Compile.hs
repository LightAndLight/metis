{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compile (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Control.Exception (SomeException, catch, fromException, throwIO)
import Data.CallStack (HasCallStack)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void (Void)
import ErrorReporting (hunitFailureToResult)
import Metis.Compile (ProgramError (..), ProgramResult (..), Stdin (..), Stdout (..), assemble, compile, runProgram)
import qualified Metis.Core as Core
import qualified Metis.Kind as Kind
import qualified Metis.Literal as Literal
import qualified Metis.Type as Type
import qualified System.Directory as Directory
import System.FilePath ((</>))
import qualified System.FilePath as FilePath
import System.IO.Temp (withSystemTempDirectory)
import qualified Test.HUnit.Lang as HUnit
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.Core.Format (FailureReason (..))
import Test.Hspec.Core.Spec (ResultStatus (..))

withTempDir :: FilePath -> (FilePath -> IO a) -> IO a
withTempDir template m =
  withSystemTempDirectory template $ \tempDir ->
    m tempDir
      `catch` ( \(input :: SomeException) -> do
                  let resultsDir = failuresLocation </> FilePath.takeBaseName tempDir
                  let message = "\nTemporary files saved in " <> resultsDir <> "\n\n"
                  _ <- runProgram "rm" ["-r", resultsDir] NoStdin IgnoreStdout
                  _ <- runProgram "mkdir" ["-p", failuresLocation] NoStdin IgnoreStdout
                  _ <- runProgram "mv" [tempDir, failuresLocation] NoStdin IgnoreStdout
                  let
                    output
                      | Just e <- fromException @HUnit.HUnitFailure input = hunitFailureToResult (Just message) e
                      | otherwise = Failure Nothing $ Error (Just message) input
                  throwIO output
              )
  where
    failuresLocation = "./test-failures"

spec :: Spec
spec =
  describe "Test.Compile" $ do
    describe "assemble" $ do
      it "success - empty" $ do
        result <- assemble "/dev/null" ""
        result `shouldBe` Right ProgramResult{stdout = ()}
      it "success - mov $1, %rax" $ do
        result <- assemble "/dev/null" "mov $1, %rax"
        result `shouldBe` Right ProgramResult{stdout = ()}
      it "error - mov x" $ do
        result <- assemble "/dev/null" "mov x\n"
        result
          `shouldBe` Left
            ProgramError
              { status = 1
              , stdout = ""
              , stderr =
                  Text.unlines
                    [ "{standard input}: Assembler messages:"
                    , "{standard input}:1: Error: number of operands mismatch for `mov'"
                    ]
              }

    describe "compile and run" $ do
      let
        shouldEvaluateTo :: (HasCallStack) => ([Core.Function], Core.Expr Void Void) -> Either ProgramError (ProgramResult Text) -> IO ()
        shouldEvaluateTo (definitions, expr) expected =
          withTempDir "metis-test-compile" $ \tempDir -> do
            let outPath = tempDir </> "program"

            compile tempDir definitions expr outPath

            outPathExists <- Directory.doesFileExist outPath
            outPathExists `shouldBe` True

            result <- runProgram outPath [] NoStdin CaptureStdout

            result `shouldBe` expected

      it "1 + 2" $
        ( []
        , Core.Add Type.Uint64 (Core.Literal $ Literal.Uint64 1) (Core.Literal $ Literal.Uint64 2)
        )
          `shouldEvaluateTo` Right ProgramResult{stdout = "3\n"}
      it "22 - 4" $
        ( []
        , Core.Subtract Type.Uint64 (Core.Literal $ Literal.Uint64 22) (Core.Literal $ Literal.Uint64 4)
        )
          `shouldEvaluateTo` Right ProgramResult{stdout = "18\n"}
      it "fn f(x : Uint64, y : Uint64) : Uint64 = x + y; fn main() = let x = 1; let y = 2; x + f(x, y)" $
        (
          [ Core.Function
              { name = "f"
              , tyArgs = []
              , args = [("x", Type.Uint64), ("y", Type.Uint64)]
              , retTy = Type.Uint64
              , body =
                  Core.Add
                    Type.Uint64
                    (Core.Var 0)
                    (Core.Var 1)
              }
          ]
        , Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Add Type.Uint64 (Core.Var . F $ B ()) (Core.Call Type.Uint64 (Core.Name "f") [] [Core.Var . F $ B (), Core.Var $ B ()])
        )
          `shouldEvaluateTo` Right ProgramResult{stdout = "4\n"}

      it "fn id @(a : Type) (x : a) : a = x; fn main() = let x = id @Uint64 99; x + 1" $
        (
          [ Core.Function
              { name = "id"
              , tyArgs = [("a", Kind.Type)]
              , args = [("x", Type.Var 0)]
              , retTy = Type.Var 0
              , body = Core.Var 0
              }
          ]
        , Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Call Type.Uint64 (Core.Name "id") [Type.Uint64] [Core.Literal $ Literal.Uint64 99]) . toScope $
            Core.Add Type.Uint64 (Core.Var (B ())) (Core.Literal $ Literal.Uint64 1)
        )
          `shouldEvaluateTo` Right ProgramResult{stdout = "100\n"}

      it "fn id @(a : Type) (x : a) : a = x; fn main() = id @Uint99 (id @Uint64 99 + 1) + 1" $
        (
          [ Core.Function
              { name = "id"
              , tyArgs = [("a", Kind.Type)]
              , args = [("x", Type.Var 0)]
              , retTy = Type.Var 0
              , body = Core.Var 0
              }
          ]
        , Core.Add
            Type.Uint64
            ( Core.Call
                Type.Uint64
                (Core.Name "id")
                [Type.Uint64]
                [ Core.Add
                    Type.Uint64
                    ( Core.Call
                        Type.Uint64
                        (Core.Name "id")
                        [Type.Uint64]
                        [Core.Literal $ Literal.Uint64 99]
                    )
                    (Core.Literal $ Literal.Uint64 1)
                ]
            )
            (Core.Literal $ Literal.Uint64 1)
        )
          `shouldEvaluateTo` Right ProgramResult{stdout = "101\n"}