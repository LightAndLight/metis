{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compile (spec) where

import Control.Applicative ((<|>))
import Control.Exception (Exception, SomeException, catch, fromException, throwIO)
import Data.CallStack (SrcLoc, srcLocFile, srcLocStartCol, srcLocStartLine)
import qualified Data.Text as Text
import Data.Typeable (Typeable)
import Metis.Compile (ProgramError (..), ProgramResult (..), Stdin (..), Stdout (..), assemble, compile, runProgram)
import qualified Metis.Core as Core
import qualified Metis.Literal as Literal
import qualified Metis.Type as Type
import qualified System.Directory as Directory
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import qualified Test.HUnit.Lang as HUnit
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.Core.Format (FailureReason (..))
import Test.Hspec.Core.Spec (Location (..), ResultStatus (..))

data ExceptionWithSnapshot = ExceptionWithSnapshot String SomeException
  deriving (Typeable)

instance Show ExceptionWithSnapshot where
  show (ExceptionWithSnapshot message exception) = message <> "\n\n" <> show exception

instance Exception ExceptionWithSnapshot

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
      it "1 + 2" . withSystemTempDirectory "metis-test-compile" $ \tempDir ->
        ( do
            let expr = Core.Add Type.Uint64 (Core.Literal $ Literal.Uint64 1) (Core.Literal $ Literal.Uint64 2)
            let outPath = tempDir </> "program"

            compile tempDir expr outPath

            outPathExists <- Directory.doesFileExist outPath
            outPathExists `shouldBe` True

            result <- runProgram outPath [] NoStdin CaptureStdout

            result `shouldBe` Right ProgramResult{stdout = "3\n"}
        )
          `catch` ( \(e :: SomeException) -> do
                      let resultsParent = "./test-failures/Test.Compile/compile-and-run"
                      let resultsDir = resultsParent </> "1-+-3"
                      let message = "\nTemporary files saved in " <> resultsDir <> "\n\n"
                      _ <- runProgram "rm" ["-r", resultsDir] NoStdin IgnoreStdout
                      _ <- runProgram "mkdir" ["-p", resultsParent] NoStdin IgnoreStdout
                      _ <- runProgram "mv" [tempDir, resultsDir] NoStdin IgnoreStdout
                      case () of
                        ()
                          | Just e' <- fromException @HUnit.HUnitFailure e -> throwIO $ hunitFailureToResult (Just message) e'
                          | otherwise -> throwIO $ Failure Nothing $ Error (Just message) e
                  )

-- the following code is taken from [`hspec-core`](https://github.com/hspec/hspec/blob/5e1fb3bb510883f7712b8d80ac377906ddf5f694/hspec-core/src/Test/Hspec/Core/Example.hs#L159).

hunitFailureToResult :: Maybe String -> HUnit.HUnitFailure -> ResultStatus
hunitFailureToResult pre e = case e of
  HUnit.HUnitFailure mLoc err ->
    case err of
      HUnit.Reason reason -> Failure location (Reason $ addPre reason)
      HUnit.ExpectedButGot preface expected actual -> Failure location (ExpectedButGot (addPreMaybe preface) expected actual)
        where
          addPreMaybe :: Maybe String -> Maybe String
          addPreMaybe xs = case (pre, xs) of
            (Just x, Just y) -> Just (x ++ "\n" ++ y)
            _ -> pre <|> xs
    where
      location = case mLoc of
        Nothing -> Nothing
        Just loc -> Just $ toLocation loc
  where
    addPre :: String -> String
    addPre xs = case pre of
      Just x -> x ++ "\n" ++ xs
      Nothing -> xs

toLocation :: SrcLoc -> Location
toLocation loc = Location (srcLocFile loc) (srcLocStartLine loc) (srcLocStartCol loc)