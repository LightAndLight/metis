{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module ErrorReporting (saveLogsOnFailure, hunitFailureToResult) where

import Control.Applicative ((<|>))
import Control.Exception (SomeException, catch, fromException, throwIO)
import Data.CallStack (SrcLoc, srcLocFile, srcLocStartCol, srcLocStartLine)
import Metis.Compile (Stdin (..), Stdout (..), runProgram)
import System.FilePath ((</>))
import qualified System.FilePath as FilePath
import qualified Test.HUnit.Lang as HUnit
import Test.Hspec.Core.Format (FailureReason (..))
import Test.Hspec.Core.Spec (Location (..), ResultStatus (..))

saveLogsOnFailure :: FilePath -> IO a -> IO a
saveLogsOnFailure logsSrc m =
  m
    `catch` ( \(input :: SomeException) -> do
                let failuresLocation = "./test-failures/"
                let resultPath = failuresLocation </> FilePath.takeFileName logsSrc
                let message = "\nLogs saved in " <> resultPath <> "\n\n"
                _ <- runProgram "mkdir" ["-p", failuresLocation] NoStdin IgnoreStdout
                _ <- runProgram "mv" [logsSrc, resultPath] NoStdin IgnoreStdout
                let
                  output
                    | Just e <- fromException @HUnit.HUnitFailure input = hunitFailureToResult (Just message) e
                    | otherwise = Failure Nothing $ Error (Just message) input
                throwIO output
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