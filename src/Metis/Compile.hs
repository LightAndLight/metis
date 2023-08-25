{-# LANGUAGE GADTs #-}
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

import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Text (Text)
import qualified Data.Text.IO as Text.IO
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as Text.Lazy.IO
import Data.Void (Void, absurd)
import Data.Word (Word64)
import Metis.AllocateRegisters (Location (..), allocateRegisters_X86_64)
import qualified Metis.Anf as Anf
import qualified Metis.Asm as Asm
import Metis.Codegen (printInstruction_X86_64)
import qualified Metis.Core as Core
import Metis.Isa (Memory (..), Op2 (..), Symbol (..), call, generalPurposeRegisters, imm, lea, mov, xor)
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Liveness as Liveness
import Metis.Log (noLogging)
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

assemble :: (MonadIO m) => FilePath -> Builder -> m (Either ProgramError (ProgramResult ()))
assemble outFile asm =
  runProgram "as" ["-o", outFile] (BuilderStdin asm) IgnoreStdout

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

compile :: (MonadIO m) => FilePath -> Core.Expr Void -> FilePath -> m ()
compile buildDir expr outPath = do
  liftIO $ Directory.createDirectoryIfMissing True buildDir

  let programName = FilePath.takeBaseName outPath

  let anf = Anf.fromCore absurd expr
  let liveness = Liveness.liveness anf
  (asm, resultLocation) <- noLogging $ allocateRegisters_X86_64 (generalPurposeRegisters @X86_64) anf liveness
  asmText <-
    fmap (Asm.printAsm printInstruction_X86_64) . Asm.runAsmBuilderT $ do
      formatString <- Asm.string "%u\n"
      _ <-
        Asm.block "main" [Asm.Global] $
          asm
            <> [ lea Op2{src = formatString, dest = Rdi}
               , case resultLocation of
                  Register register -> mov Op2{src = register, dest = Rsi}
                  Stack offset -> mov Op2{src = Mem{base = Rbp, offset}, dest = Rsi}
               , xor Op2{src = Rax, dest = Rax}
               , call (Symbol "printf")
               , mov Op2{src = imm (0 :: Word64), dest = Rdi}
               , call (Symbol "exit")
               ]
      pure ()

  let objectFile = buildDir </> programName <.> "o"
  assembleResult <- assemble objectFile asmText
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