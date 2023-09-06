{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.InstSelection (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Control.Monad (void)
import Control.Monad.State.Class (modify)
import Control.Monad.State.Strict (evalState)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy (Text)
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import Data.Void (Void, absurd)
import ErrorReporting (saveLogsOnFailure)
import qualified Metis.Anf as Anf
import Metis.Asm (BlockAttribute (..), printAsm)
import Metis.Asm.Builder (runAsmBuilderT)
import Metis.Codegen (printInstruction_X86_64)
import qualified Metis.Core as Core
import Metis.InstSelection (
  InstSelectionState (..),
  Location (..),
  RegisterFunctionArgument (..),
  Value (..),
  initialInstSelectionState,
  instSelectionFunction_X86_64,
  instSelection_X86_64,
  moveRegisterFunctionArguments,
 )
import Metis.Isa (Op2 (..), generalPurposeRegisters, mov)
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Literal as Literal
import qualified Metis.Liveness as Liveness
import Metis.Log (handleLogging)
import Metis.Type (Type)
import qualified Metis.Type as Type
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import Test.Hspec (HasCallStack, Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.InstSelection" $ do
    describe "moveRegisterFunctionArguments" $ do
      it "a @ %rax, b @ %rbx |- f(b, a) : {%rbx, %rax} -> {%rax, %rbx}" $ do
        let result = flip evalState (initialInstSelectionState (generalPurposeRegisters @X86_64) mempty "main" [Global]) $ do
              modify (\s -> s{available = Seq.filter (`notElem` ([Rax, Rbx] :: [Register X86_64])) s.available})
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
              modify (\s -> s{available = Seq.filter (`notElem` ([Rax, Rbx] :: [Register X86_64])) s.available})
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
        shouldCompileTo :: (HasCallStack) => (HashMap Text (Type Anf.Var), Core.Expr Void Void) -> [Lazy.Text] -> IO ()
        shouldCompileTo (nameTys, expr) expectedOutput =
          withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
            saveLogsOnFailure tempFilePath $ do
              let (anfInfo, anf) = Anf.fromCore (nameTys HashMap.!) absurd absurd expr
              let liveness = Liveness.liveness anf

              asm <-
                fmap (printAsm printInstruction_X86_64) . runAsmBuilderT . handleLogging tempFileHandle . void $
                  instSelection_X86_64 (nameTys HashMap.!) (generalPurposeRegisters @X86_64) anfInfo anf liveness "main" [Global]

              hClose tempFileHandle

              Builder.toLazyText asm `shouldBe` Text.Lazy.unlines expectedOutput

      it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; f(x, y)" $
        ( [("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)]
        , Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Call Type.Uint64 (Core.Name "f") [] [Core.Var . F $ B (), Core.Var $ B ()]
        )
          `shouldCompileTo` [ ".text"
                            , ".global main"
                            , "main:"
                            , "mov $1, %rax"
                            , "mov $2, %rbx"
                            , "push $after"
                            , "push %rbp"
                            , "mov %rsp, %rbp"
                            , "jmp f"
                            , "after:"
                            ]

      it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; let z = f(x, y); x + z" $
        ( [("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)]
        , Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Let Type.Uint64 (Just "z") Type.Uint64 (Core.Call Type.Uint64 (Core.Name "f") [] [Core.Var . F $ B (), Core.Var $ B ()]) . toScope $
                Core.Add Type.Uint64 (Core.Var . F . F $ B ()) (Core.Var $ B ())
        )
          `shouldCompileTo` [ ".text"
                            , ".global main"
                            , "main:"
                            , "mov $1, %rax"
                            , "mov $2, %rbx"
                            , "push %rax"
                            , "push $after"
                            , "push %rbp"
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
        ( [("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)]
        , Core.Let Type.Uint64 (Just "x") Type.Uint64 (Core.Literal $ Literal.Uint64 1) . toScope $
            Core.Let Type.Uint64 (Just "y") Type.Uint64 (Core.Literal $ Literal.Uint64 2) . toScope $
              Core.Let Type.Uint64 (Just "z") Type.Uint64 (Core.Call Type.Uint64 (Core.Name "f") [] [Core.Var $ B (), Core.Var . F $ B ()]) . toScope $
                Core.Add Type.Uint64 (Core.Var . F . F $ B ()) (Core.Var $ B ())
        )
          `shouldCompileTo` [ ".text"
                            , ".global main"
                            , "main:"
                            , "mov $1, %rax"
                            , "mov $2, %rbx"
                            , "push %rax"
                            , "push $after"
                            , -- begin argument setup
                              "mov %rax, %rcx"
                            , "mov %rbx, %rax"
                            , "mov %rcx, %rbx"
                            , -- end argument setup
                              "push %rbp"
                            , "mov %rsp, %rbp"
                            , "jmp f"
                            , "after:"
                            , -- move result out of the way
                              -- `%rbx` is killed by the call, so is the next allocation candidate
                              "mov %rax, %rbx"
                            , "pop %rax"
                            , "add %rbx, %rax"
                            ]
    describe "instSelectionFunction_X86_64" $ do
      let
        shouldCompileTo' :: (HasCallStack) => Seq (Register X86_64) -> Core.Function -> [Lazy.Text] -> IO ()
        shouldCompileTo' available function expectedOutput =
          withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
            saveLogsOnFailure tempFilePath $ do
              let function' = Anf.fromFunction (const undefined) function
              let liveness = Liveness.liveness function'.body
              let nameTys = \case
                    "f" -> Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64
                    _ -> undefined

              asm <-
                fmap (printAsm printInstruction_X86_64) . runAsmBuilderT . handleLogging tempFileHandle . void $
                  instSelectionFunction_X86_64 nameTys available liveness function'

              hClose tempFileHandle

              Builder.toLazyText asm `shouldBe` Text.Lazy.unlines expectedOutput

        shouldCompileTo :: (HasCallStack) => Core.Function -> [Lazy.Text] -> IO ()
        shouldCompileTo = shouldCompileTo' (generalPurposeRegisters @X86_64)

      it "f(x : Uint64, y : Uint64) : Uint64 = x + y" $
        Core.Function
          { name = "f"
          , tyArgs = []
          , args = [("x", Type.Uint64), ("y", Type.Uint64)]
          , retTy = Type.Uint64
          , body = Core.Add Type.Uint64 (Core.Var 0) (Core.Var 1)
          }
          `shouldCompileTo` [ ".text"
                            , "f:"
                            , "add %rbx, %rax"
                            , "pop %rbp"
                            , "ret"
                            ]

      it "f(x : Uint64, y : Uint64) : Uint64 = x + y (only %rax available)" $
        shouldCompileTo'
          (fromList [Rax])
          Core.Function
            { name = "f"
            , tyArgs = []
            , args = [("x", Type.Uint64), ("y", Type.Uint64)]
            , retTy = Type.Uint64
            , body = Core.Add Type.Uint64 (Core.Var 0) (Core.Var 1)
            }
          [ ".text"
          , "f:"
          , -- `y` is passed via stack
            "add 8(%rbp), %rax"
          , "pop %rbp"
          , "add $8, %rsp" -- deallocate `y`
          , "ret"
          ]

      it "f(x : Uint64, y : Uint64, z : Uint64) : Uint64 = x + y + z (only %rax available)" $
        shouldCompileTo'
          (fromList [Rax])
          Core.Function
            { name = "f"
            , tyArgs = []
            , args = [("x", Type.Uint64), ("y", Type.Uint64), ("z", Type.Uint64)]
            , retTy = Type.Uint64
            , body = Core.Add Type.Uint64 (Core.Add Type.Uint64 (Core.Var 0) (Core.Var 1)) (Core.Var 2)
            }
          [ ".text"
          , "f:"
          , -- `x` is passed in register at %rax
            -- `y` is passed via stack at 8(%rbp)
            -- `z` is passed via stack at 16(%rbp)
            "add 8(%rbp), %rax"
          , "add 16(%rbp), %rax"
          , "pop %rbp"
          , "add $16, %rsp" -- deallocate `y` and `z`
          , "ret"
          ]