{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeApplications #-}

module Metis.Compile (
  compile,
  assemble,
  link,

  -- * Subprocessing
  ProgramError (..),
  ProgramResult (..),
  Stdin (..),
  Stdout (..),
  runProgram,
) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Buildable (collectL')
import Data.Char (ord)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Maybe as Maybe
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text.IO as Text.IO
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO
import qualified Data.Text.Lazy.IO as Text.Lazy.IO
import Data.Void (Void, absurd)
import LLVM.AST.Constant (Constant (..))
import LLVM.AST.Operand (Operand (..))
import LLVM.AST.ParameterAttribute (ParameterAttribute (..))
import LLVM.AST.Type (Type (..), i32, i8, ptr, void)
import LLVM.IRBuilder.Instruction (bitcast, call, retVoid)
import LLVM.IRBuilder.Module (buildModule, extern, externVarArgs, function, global)
import LLVM.Pretty (ppllvm)
import qualified Metis.Core as Core
import Metis.LLVM (llvmExpr, llvmFunction, llvmTypeDicts)
import qualified Metis.Type as Core (Type)
import qualified Metis.Type as Type
import qualified System.Directory as Directory
import qualified System.Environment
import System.Exit (ExitCode (..))
import qualified System.Exit
import System.FilePath ((<.>), (</>))
import qualified System.FilePath as FilePath
import System.IO (hClose, hPutStrLn)
import qualified System.IO
import qualified System.Process as Process

data ProgramError = ProgramError {status :: Int, stdout :: Text, stderr :: Text}
  deriving (Eq, Show)

data Stdout a where
  IgnoreStdout :: Stdout ()
  CaptureStdout :: Stdout Text

data Stdin where
  NoStdin :: Stdin
  BuilderStdin :: Builder -> Stdin

data ProgramResult stdout = ProgramResult {stdout :: stdout}
  deriving (Eq, Show)

runProgram ::
  (MonadIO m) =>
  FilePath ->
  [String] ->
  Stdin ->
  Stdout stdout ->
  m (Either ProgramError (ProgramResult stdout))
runProgram program args handleStdin handleStdout =
  liftIO $
    Process.withCreateProcess
      ( (Process.proc program args)
          { Process.std_in = Process.CreatePipe
          , Process.std_out = Process.CreatePipe
          , Process.std_err = Process.CreatePipe
          }
      )
      ( \mStdin mStdout mStderr processHandle ->
          case (mStdin, mStdout, mStderr) of
            (Nothing, _, _) -> error "missing stdin handle"
            (_, Nothing, _) -> error "missing stdout handle"
            (_, _, Nothing) -> error "missing stderr handle"
            (Just stdin, Just stdout, Just stderr) -> do
              case handleStdin of
                NoStdin ->
                  pure ()
                BuilderStdin input ->
                  Text.Lazy.IO.hPutStr stdin (Builder.toLazyText input)
              hClose stdin

              exitStatus <- Process.waitForProcess processHandle
              case exitStatus of
                ExitSuccess -> do
                  stdoutContents <- case handleStdout of
                    IgnoreStdout ->
                      hClose stdout
                    CaptureStdout ->
                      Text.IO.hGetContents stdout
                  pure $ Right ProgramResult{stdout = stdoutContents}
                ExitFailure status -> do
                  stdoutContents <- Text.IO.hGetContents stdout
                  hClose stdout

                  stderrContents <- Text.IO.hGetContents stderr
                  hClose stderr

                  pure $ Left ProgramError{status, stdout = stdoutContents, stderr = stderrContents}
      )

assemble :: (MonadIO m) => FilePath -> FilePath -> m (Either ProgramError (ProgramResult ()))
assemble asmFile outFile =
  runProgram "as" [asmFile, "-o", outFile] NoStdin IgnoreStdout

link :: (MonadIO m) => FilePath -> FilePath -> m (Either ProgramError (ProgramResult ()))
link inFile outFile = do
  {-
  -I: Set the program's dynamic linker.
      `$LIBC_LIB_PATH` is an environment variable I added to the Nix shell.

  -L: Tell the linker to search this path when resolving symbols.
      `$LIBC_LIB_PATH/lib` contains `libc.so`, among others.

  -l c: Allow the linker to see symbols in `libc.so` from library search path.
  -}
  libcLibPath <- liftIO $ System.Environment.getEnv "LIBC_LIB_PATH"
  runProgram
    "ld"
    ( ["-I", libcLibPath <> "/lib/ld-linux-x86-64.so.2"]
        <> ["-L", libcLibPath <> "/lib"]
        <> ["-l", "c"]
        <> ["-m", "elf_x86_64"]
        <> ["-e", "main"]
        <> [inFile]
        <> ["-o", outFile]
    )
    NoStdin
    IgnoreStdout

compile :: (MonadFix m, MonadIO m) => FilePath -> [Core.Function] -> Core.Expr Void Void -> FilePath -> m ()
compile buildDir definitions expr outPath = do
  liftIO $ Directory.createDirectoryIfMissing True buildDir

  let programName = FilePath.takeBaseName outPath

  let
    coreNameTysMap :: HashMap Text (Core.Type a)
    coreNameTysMap =
      collectL' @(HashMap _ _) $
        fmap
          ( \Core.Function{name, tyArgs, args, retTy} ->
              (name, Type.forall_ tyArgs (Type.Fn (fmap snd args) retTy))
          )
          definitions

    coreNameTys :: Text -> Core.Type a
    coreNameTys name = Maybe.fromMaybe (error $ show name <> " missing from core name types map") $ HashMap.lookup name coreNameTysMap

  llvm <- do
    let llvmText = ppllvm . buildModule (fromString programName) $ do
          typeDicts <- llvmTypeDicts
          rec definitions' <-
                traverse
                  ( \fn ->
                      (,) fn.name
                        <$> llvmFunction
                          coreNameTys
                          typeDicts
                          nameOperand
                          fn
                  )
                  definitions
              let nameOperand = ConstantOperand . (collectL' @(HashMap _ _) definitions' HashMap.!)

          cprintf <- externVarArgs "printf" [ptr i8 {- void -}] void

          let s = "%u\n\0" :: String
          formatString <-
            global
              "formatString"
              ArrayType{nArrayElements = fromIntegral $ length s, elementType = i8}
              Array{memberType = i8, memberValues = fmap (\c -> Int{integerBits = 8, integerValue = fromIntegral $ ord c}) s}

          cexit <- extern "exit" [i32] void

          function "main" [] void $ \_ -> do
            result <- llvmExpr coreNameTys absurd absurd typeDicts nameOperand absurd absurd expr
            formatString' <- bitcast formatString (ptr i8)
            _ <- call cprintf [(formatString', [NoCapture]), (result, [])]
            _ <- call cexit [(ConstantOperand Int{integerBits = 32, integerValue = 0}, [])]
            retVoid
    let llvm = buildDir </> programName <.> "ll"
    liftIO $ Data.Text.Lazy.IO.writeFile llvm llvmText
    pure llvm

  asm <- do
    let asm = buildDir </> programName <.> "s"
    llcResult <- runProgram "llc" [llvm, "--filetype=asm", "-o", asm] NoStdin IgnoreStdout
    case llcResult of
      Right _ -> pure ()
      Left ProgramError{status, stdout, stderr} ->
        liftIO $ do
          hPutStrLn System.IO.stderr $ "`llc` exited with status " <> show status

          hPutStrLn System.IO.stderr ""

          hPutStrLn System.IO.stderr "stdout:"
          Text.IO.hPutStrLn System.IO.stderr stdout

          hPutStrLn System.IO.stderr ""

          hPutStrLn System.IO.stderr "stderr:"
          Text.IO.hPutStrLn System.IO.stderr stderr

          System.Exit.exitFailure
    pure asm

  -- TODO: this was helpful for debugging some bad ASM. Perhaps it should be a compile option?
  -- liftIO $ Text.Lazy.IO.writeFile (buildDir </> programName <.> "s") (Builder.toLazyText asm)

  let objectFile = buildDir </> programName <.> "o"
  assembleResult <- assemble asm objectFile
  case assembleResult of
    Right _ -> pure ()
    Left ProgramError{status, stdout, stderr} ->
      liftIO $ do
        hPutStrLn System.IO.stderr $ "`as` exited with status " <> show status

        hPutStrLn System.IO.stderr ""

        hPutStrLn System.IO.stderr "stdout:"
        Text.IO.hPutStrLn System.IO.stderr stdout

        hPutStrLn System.IO.stderr ""

        hPutStrLn System.IO.stderr "stderr:"
        Text.IO.hPutStrLn System.IO.stderr stderr

        System.Exit.exitFailure

  let binaryFile = buildDir </> programName
  linkResult <- link objectFile binaryFile
  case linkResult of
    Right _ -> pure ()
    Left ProgramError{status, stdout, stderr} ->
      liftIO $ do
        hPutStrLn System.IO.stderr $ "`ld` exited with status " <> show status

        hPutStrLn System.IO.stderr ""

        hPutStrLn System.IO.stderr "stdout:"
        Text.IO.hPutStrLn System.IO.stderr stdout

        hPutStrLn System.IO.stderr ""

        hPutStrLn System.IO.stderr "stderr:"
        Text.IO.hPutStrLn System.IO.stderr stderr

        System.Exit.exitFailure

  liftIO $ do
    permissions <- Directory.getPermissions binaryFile
    Directory.setPermissions binaryFile (Directory.setOwnerExecutable True permissions)

  liftIO $ Directory.copyFile binaryFile outPath