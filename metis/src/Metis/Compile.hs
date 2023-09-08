{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedRecordDot #-}
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
import Data.Foldable (for_)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import qualified Data.Text.IO as Text.IO
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as Text.Lazy.IO
import Data.Void (Void, absurd)
import Data.Word (Word64)
import qualified Metis.Anf as Anf
import Metis.Asm (Statement (..))
import qualified Metis.Asm as Asm (printAsm)
import qualified Metis.Asm.Builder as Asm (runAsmBuilderT)
import qualified Metis.Asm.Class as Asm (block, string)
import Metis.Codegen (printInstruction_X86_64)
import qualified Metis.Core as Core
import Metis.InstSelection (Address (..), Location (..), Value (..), instSelectionEntrypoint_X86_64, instSelectionFunction_X86_64)
import Metis.Isa (Memory (..), MemoryBase (..), Op2 (..), Symbol (..), call, generalPurposeRegisters, imm, lea, load, mov, xor)
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Liveness as Liveness
import Metis.Log (noLogging)
import Metis.Type (Type)
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

compile :: (MonadFix m, MonadIO m) => FilePath -> [Core.Function] -> Core.Expr Void Void -> FilePath -> m ()
compile buildDir definitions expr outPath = do
  liftIO $ Directory.createDirectoryIfMissing True buildDir

  let programName = FilePath.takeBaseName outPath

  let
    coreNameTysMap :: HashMap Text (Type a)
    coreNameTysMap =
      collectL' @(HashMap _ _) $
        fmap
          ( \Core.Function{name, tyArgs, args, retTy} ->
              (name, Type.forall_ tyArgs (Type.Fn (fmap snd args) retTy))
          )
          definitions

    coreNameTys :: Text -> Type a
    coreNameTys name = Maybe.fromMaybe (error $ show name <> " missing from core name types map") $ HashMap.lookup name coreNameTysMap

  let availableRegisters = generalPurposeRegisters @X86_64
  asm <- fmap (Asm.printAsm printInstruction_X86_64) . Asm.runAsmBuilderT . noLogging $ do
    let anfDefinitions = fmap (Anf.fromFunction coreNameTys) definitions

    let
      anfNameTysMap :: HashMap Text (Type Anf.Var)
      anfNameTysMap =
        collectL' @(HashMap _ _) $
          fmap
            (\Anf.Function{name, args, retTy} -> (name, Type.Fn (fmap snd args) retTy))
            anfDefinitions

      anfNameTys :: Text -> Type Anf.Var
      anfNameTys name = Maybe.fromMaybe (error $ show name <> " missing from anf name types map") $ HashMap.lookup name anfNameTysMap

    for_ anfDefinitions $ \anfFunction -> do
      let liveness = Liveness.liveness anfFunction.body
      instSelectionFunction_X86_64 anfNameTys availableRegisters liveness anfFunction

    resultValue <- do
      let (anfInfo, anf) = Anf.fromCore anfNameTys absurd absurd expr
      let liveness = Liveness.liveness anf
      instSelectionEntrypoint_X86_64 anfNameTys availableRegisters liveness "main" anf anfInfo

    formatString <- Asm.string "%u\n"
    _ <-
      Asm.block
        "print_and_exit"
        []
        Nothing
        ( fmap
            Instruction
            [ lea Op2{src = formatString, dest = Rdi}
            , case resultValue of
                ValueAt (Register register) -> mov Op2{src = register, dest = Rsi}
                ValueAt Stack{offset, size = _} -> load Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = Rsi}
                AddressOf (Metis.InstSelection.Symbol symbol) -> mov Op2{src = imm symbol, dest = Rsi}
                AddressOf (Memory mem) -> lea Op2{src = mem, dest = Rsi}
                Literal lit -> mov Op2{src = imm lit, dest = Rsi}
            , xor Op2{src = Rax, dest = Rax}
            , call (Metis.Isa.Symbol "printf")
            , mov Op2{src = imm (0 :: Word64), dest = Rdi}
            , call (Metis.Isa.Symbol "exit")
            ]
        )
    pure ()

  -- TODO: this was helpful for debugging some bad ASM. Perhaps it should be a compile option?
  -- liftIO $ Text.Lazy.IO.writeFile (buildDir </> programName <.> "s") (Builder.toLazyText asm)

  let objectFile = buildDir </> programName <.> "o"
  assembleResult <- assemble objectFile asm
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