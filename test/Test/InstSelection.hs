{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.InstSelection (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Control.Exception (SomeException, catch, fromException, throwIO)
import Control.Monad (void)
import Control.Monad.State.Class (modify)
import Control.Monad.State.Strict (evalState)
import Data.Sequence as Seq
import qualified Data.Text.Lazy as Lazy (Text)
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import Data.Void (Void, absurd)
import ErrorReporting (hunitFailureToResult)
import qualified Metis.Anf as Anf
import Metis.Asm (BlockAttribute (..), printAsm)
import Metis.Asm.Builder (runAsmBuilderT)
import Metis.Codegen (printInstruction_X86_64)
import Metis.Compile (Stdin (..), Stdout (..), runProgram)
import qualified Metis.Core as Core
import Metis.InstSelection (
  InstSelectionState (..),
  Location (..),
  RegisterFunctionArgument (..),
  Value (..),
  initialInstSelectionState,
  instSelection_X86_64,
  moveRegisterFunctionArguments,
 )
import Metis.Isa (Isa (generalPurposeRegisters), Op2 (..), mov)
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Literal as Literal
import qualified Metis.Liveness as Liveness
import Metis.Log (handleLogging)
import qualified Metis.Type as Type
import System.FilePath ((</>))
import qualified System.FilePath as FilePath
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import qualified Test.HUnit.Lang as HUnit
import Test.Hspec (HasCallStack, Spec, describe, it, shouldBe)
import Test.Hspec.Core.Spec (FailureReason (..), ResultStatus (..))

spec :: Spec
spec =
  describe "Test.InstSelection" $ do
    describe "moveRegisterFunctionArguments" $ do
      it "a @ %rax, b @ %rbx |- f(b, a) : {%rbx, %rax} -> {%rax, %rbx}" $ do
        let result = flip evalState (initialInstSelectionState (generalPurposeRegisters @X86_64) mempty "main" [Global]) $ do
              modify (\s -> s{available = Seq.filter (`notElem` [Rax, Rbx]) s.available})
              moveRegisterFunctionArguments
                mempty
                [ RegisterFunctionArgument{size = 8, src = ValueAt $ Register Rbx, dest = Rax}
                , RegisterFunctionArgument{size = 8, src = ValueAt $ Register Rax, dest = Rbx}
                ]

        result
          `shouldBe` [
                       -- save destination to temporary
                       mov Op2{src = Rax, dest = Rcx}
                     , -- write value to destination
                       mov Op2{src = Rbx, dest = Rax}
                     , -- `Rax` should now be considered remapped to `Rcx`
                       {- No need to save the final destination to a temporary.
                       , mov Op2{src = Rbx, dest = Rdx} -- save destination to temporary
                       -}
                       -- write value to destination
                       mov Op2{src = Rcx {- Rax remapped -}, dest = Rbx}
                     ]
      it "a @ %rax, b @ %rbx |- f(b, a, b) : {%rbx, %rax, %rbx} -> {%rax, %rbx, %rcx}" $ do
        let result = flip evalState (initialInstSelectionState (generalPurposeRegisters @X86_64) mempty "main" [Global]) $ do
              modify (\s -> s{available = Seq.filter (`notElem` [Rax, Rbx]) s.available})
              moveRegisterFunctionArguments
                mempty
                [ RegisterFunctionArgument{size = 8, src = ValueAt $ Register Rbx, dest = Rax}
                , RegisterFunctionArgument{size = 8, src = ValueAt $ Register Rax, dest = Rbx}
                , RegisterFunctionArgument{size = 8, src = ValueAt $ Register Rbx, dest = Rcx}
                ]

        result
          `shouldBe` [
                       -- save destination to temporary
                       mov Op2{src = Rax, dest = Rcx}
                     , -- write value to destination
                       mov Op2{src = Rbx, dest = Rax}
                     , -- `Rax` should now be considered remapped to `Rcx`
                       -- save destination to temporary
                       mov Op2{src = Rbx, dest = Rdx}
                     , -- write value to destination
                       mov Op2{src = Rcx {- Rax remapped -}, dest = Rbx}
                     , -- `Rbx` should now be considered remapped to `Rdx`
                       -- write value to destination
                       mov Op2{src = Rdx {- Rbx remapped -}, dest = Rcx}
                     ]
    describe "instSelection_X86_64" $ do
      let
        shouldCompileTo :: (HasCallStack) => Core.Expr Void -> [Lazy.Text] -> IO ()
        shouldCompileTo expr expectedOutput =
          withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
            ( do
                let (anfInfo, anf) = Anf.fromCore absurd expr
                let liveness = Liveness.liveness anf
                let nameTys = \case
                      "f" -> Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64
                      _ -> undefined

                asm <-
                  fmap (printAsm printInstruction_X86_64) . runAsmBuilderT . handleLogging tempFileHandle . void $
                    instSelection_X86_64 nameTys (generalPurposeRegisters @X86_64) anfInfo anf liveness "main" [Global]

                hClose tempFileHandle

                Builder.toLazyText asm `shouldBe` Text.Lazy.unlines expectedOutput
            )
              `catch` ( \(input :: SomeException) -> do
                          let failuresLocation = "./test-failures/"
                          let resultPath = failuresLocation </> FilePath.takeFileName tempFilePath
                          let message = "\nLogs saved in " <> resultPath <> "\n\n"
                          _ <- runProgram "mkdir" ["-p", failuresLocation] NoStdin IgnoreStdout
                          _ <- runProgram "mv" [tempFilePath, resultPath] NoStdin IgnoreStdout
                          let
                            output
                              | Just e <- fromException @HUnit.HUnitFailure input = hunitFailureToResult (Just message) e
                              | otherwise = Failure Nothing $ Error (Just message) input
                          throwIO output
                      )

      it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; f(x, y)" $
        ( Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Call Type.Uint64 (Core.Name "f") [Core.Var . F $ B (), Core.Var $ B ()]
        )
          `shouldCompileTo` [ ".text"
                            , ".global main"
                            , "main:"
                            , "mov $1, %rax"
                            , "mov $2, %rbx"
                            , "push %rbp"
                            , "push $after"
                            , "mov %rsp, %rbp"
                            , "jmp f"
                            , "after:"
                            ]

      it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; let z = f(x, y); x + z" $
        ( Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Let Type.Uint64 (Just "z") Type.Uint64 (Core.Call Type.Uint64 (Core.Name "f") [Core.Var . F $ B (), Core.Var $ B ()]) . toScope $
                Core.Add Type.Uint64 (Core.Var . F . F $ B ()) (Core.Var $ B ())
        )
          `shouldCompileTo` [ ".text"
                            , ".global main"
                            , "main:"
                            , "mov $1, %rax"
                            , "mov $2, %rbx"
                            , "push %rax"
                            , "push %rbp"
                            , "push $after"
                            , "mov %rsp, %rbp"
                            , "jmp f"
                            , "after:"
                            , -- move result out of the way
                              -- `%rbx` is killed by the call, so is the next candidate
                              "mov %rax, %rbx"
                            , "pop %rax"
                            , "add %rbx, %rax"
                            ]

      it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; let z = f(y, x); x + z" $
        ( Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Let Type.Uint64 (Just "z") Type.Uint64 (Core.Call Type.Uint64 (Core.Name "f") [Core.Var $ B (), Core.Var . F $ B ()]) . toScope $
                Core.Add Type.Uint64 (Core.Var . F . F $ B ()) (Core.Var $ B ())
        )
          `shouldCompileTo` [ ".text"
                            , ".global main"
                            , "main:"
                            , "mov $1, %rax"
                            , "mov $2, %rbx"
                            , "push %rax"
                            , -- begin argument setup
                              "mov %rax, %rcx"
                            , "mov %rbx, %rax"
                            , "mov %rcx, %rbx"
                            , -- end argument setup
                              "push %rbp"
                            , "push $after"
                            , "mov %rsp, %rbp"
                            , "jmp f"
                            , "after:"
                            , -- move result out of the way
                              -- `%rbx` is killed by the call, so is the next allocation candidate
                              "mov %rax, %rbx"
                            , "pop %rax"
                            , "add %rbx, %rax"
                            ]