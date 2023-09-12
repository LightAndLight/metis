{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}

module Test.CoreToAsmNew (spec) where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalStateT, runStateT)
import Data.CallStack (HasCallStack)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Sequence (Seq)
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Data.Void (Void, absurd)
import ErrorReporting (saveLogsOnFailure)
import Metis.Asm (printAsm)
import Metis.Asm.Builder (runAsmBuilderT)
import Metis.Codegen (printInstruction_X86_64)
import Metis.Core (Expr (..), Function (..))
import Metis.InstSelectionNew (initialInstSelState, instSelectionBlock)
import qualified Metis.InstSelectionNew as InstSelectionNew
import Metis.IsaNew (Register, generalPurposeRegisters)
import Metis.IsaNew.X86_64 (X86_64, allocRegisters_X86_64, instSelection_X86_64)
import Metis.Log (handleLogging)
import Metis.RegisterAllocation (AllocRegistersEnv (..), AllocRegistersState (..), allocRegisters, initialAllocRegistersState)
import qualified Metis.SSA as SSA
import Metis.Type (Type)
import System.IO.Temp (withSystemTempFile)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.CoreToAsmNew" $ do
    describe "x86-64" $ do
      let
        shouldCompileTo :: (HasCallStack) => (HashMap Text (Type Void), Expr Void Void) -> [Lazy.Text] -> IO ()
        shouldCompileTo (nameTypes, expr) expectedOutput =
          withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
            saveLogsOnFailure tempFilePath $ do
              ssa <-
                SSA.toBlocks
                  SSA.FromCoreEnv{nameTypes = (nameTypes HashMap.!)}
                  (SSA.fromCoreExpr absurd absurd expr)

              let liveness = error "TODO: liveness for SSA"

              (instsVirtual, instSelState) <-
                flip runStateT initialInstSelState $
                  traverse (instSelectionBlock instSelection_X86_64) ssa

              instsPhysical <-
                flip evalStateT initialAllocRegistersState{stackFrameTop = instSelState.stackFrameTop}
                  . flip runReaderT AllocRegistersEnv{kills = liveness}
                  $ traverse
                    ( \block ->
                        (\instructions' -> block{InstSelectionNew.instructions = instructions'})
                          <$> allocRegisters allocRegisters_X86_64 block.instructions
                    )
                    instsVirtual

              asm <-
                fmap (printAsm printInstruction_X86_64) . runAsmBuilderT . handleLogging tempFileHandle $
                  instSelection_X86_64 ssa

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
                            , "call f"
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
                            , "call f"
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
                            , -- begin argument setup
                              "mov %rax, %rcx"
                            , "mov %rbx, %rax"
                            , "mov %rcx, %rbx"
                            , -- end argument setup
                              "call f"
                            , -- move result out of the way
                              -- `%rbx` is killed by the call, so is the next allocation candidate
                              "mov %rax, %rbx"
                            , "pop %rax"
                            , "add %rbx, %rax"
                            ]
    describe "instSelectionFunction_X86_64" $ do
      let
        shouldCompileTo' :: (HasCallStack) => Seq (Register X86_64) -> Function -> [Lazy.Text] -> IO ()
        shouldCompileTo' available function expectedOutput =
          withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
            saveLogsOnFailure tempFilePath $ do
              let function' = Anf.fromFunction (const undefined) function
              let liveness = Liveness.liveness function' . body
              let nameTys = \case
                    "f" -> Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64
                    _ -> undefined

              asm <-
                fmap (printAsm printInstruction_X86_64) . runAsmBuilderT . handleLogging tempFileHandle . void $
                  instSelectionFunction_X86_64 nameTys available liveness function'

              hClose tempFileHandle

              Builder.toLazyText asm `shouldBe` Text.Lazy.unlines expectedOutput

        shouldCompileTo :: (HasCallStack) => Function -> [Lazy.Text] -> IO ()
        shouldCompileTo = shouldCompileTo' (generalPurposeRegisters @X86_64)

      it "f(x : Uint64, y : Uint64) : Uint64 = x + y" $
        Function
          { name = "f"
          , tyArgs = []
          , args = [("x", Type.Uint64), ("y", Type.Uint64)]
          , retTy = Type.Uint64
          , body = Core.Add Type.Uint64 (Core.Var 0) (Core.Var 1)
          }
          `shouldCompileTo` [ ".text"
                            , "f:"
                            , "push %rbp"
                            , "mov %rsp, %rbp"
                            , "add %rbx, %rax"
                            , "pop %rbp"
                            , "ret"
                            ]

      it "f(x : Uint64, y : Uint64) : Uint64 = x + y (only %rax available)" $
        shouldCompileTo'
          (fromList [Rax])
          Function
            { name = "f"
            , tyArgs = []
            , args = [("x", Type.Uint64), ("y", Type.Uint64)]
            , retTy = Type.Uint64
            , body = Core.Add Type.Uint64 (Core.Var 0) (Core.Var 1)
            }
          [ ".text"
          , "f:"
          , "push %rbp"
          , "mov %rsp, %rbp"
          , -- `y` is passed via stack
            "add 8(%rbp), %rax"
          , "pop %rbp"
          , "ret $8"
          ]

      it "f(x : Uint64, y : Uint64, z : Uint64) : Uint64 = x + y + z (only %rax available)" $
        shouldCompileTo'
          (fromList [Rax])
          Function
            { name = "f"
            , tyArgs = []
            , args = [("x", Type.Uint64), ("y", Type.Uint64), ("z", Type.Uint64)]
            , retTy = Type.Uint64
            , body = Core.Add Type.Uint64 (Core.Add Type.Uint64 (Core.Var 0) (Core.Var 1)) (Core.Var 2)
            }
          [ ".text"
          , "f:"
          , "push %rbp"
          , "mov %rsp, %rbp"
          , -- `x` is passed in register at %rax
            -- `y` is passed via stack at 8(%rbp)
            -- `z` is passed via stack at 16(%rbp)
            "add 8(%rbp), %rax"
          , "add 16(%rbp), %rax"
          , "pop %rbp"
          , "ret $16"
          ]