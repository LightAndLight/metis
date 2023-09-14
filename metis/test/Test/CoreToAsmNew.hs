{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}

module Test.CoreToAsmNew (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalStateT, runStateT)
import Data.CallStack (HasCallStack)
import Data.Foldable (traverse_)
import qualified Data.HashMap.Strict as HashMap
import Data.Sequence (Seq)
import qualified Data.Text.Lazy as Lazy (Text)
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import Data.Void (Void, absurd)
import ErrorReporting (saveLogsOnFailure)
import Metis.Asm.BuilderNew (runAsmBuilderT)
import qualified Metis.Asm.ClassNew as Asm (block)
import Metis.AsmNew (printAsm)
import qualified Metis.AsmNew as Asm
import Metis.Core (Expr (..), Function (..))
import Metis.InstSelectionNew (
  InstSelEnv (..),
  initialInstSelState,
  instSelectionBlock,
  instSelectionFunction,
 )
import qualified Metis.InstSelectionNew as InstSelectionNew
import Metis.IsaNew (Register, generalPurposeRegisters, printRegister)
import Metis.IsaNew.X86_64 (Register (..), X86_64, allocRegisters_X86_64, instSelection_X86_64, printInstruction_X86_64)
import qualified Metis.Literal as Literal
import Metis.LivenessNew (livenessBlocks, runLivenessT)
import Metis.Log (handleLogging)
import Metis.RegisterAllocation (
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  allocRegisters,
  allocRegistersFunction,
  initialAllocRegistersState,
 )
import qualified Metis.SSA as SSA
import Metis.SSA.Var (runVarT)
import qualified Metis.Type as Type
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.CoreToAsmNew" $ do
    describe "x86-64" $ do
      describe "expressions" $ do
        let
          shouldCompileTo :: (HasCallStack) => Expr Void Void -> [Lazy.Text] -> IO ()
          shouldCompileTo expr expectedOutput =
            withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
              saveLogsOnFailure tempFilePath $ do
                let nameTypes = [("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)]

                (liveness, instsVirtual, instSelState) <-
                  runVarT $ do
                    (varTypes, ssa) <-
                      SSA.toBlocks
                        SSA.FromCoreEnv{nameTypes = (nameTypes HashMap.!)}
                        (SSA.fromCoreExpr absurd absurd expr)

                    let ssaNameTypes = [("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)]

                    (liveness, _) <- runLivenessT $ livenessBlocks ssa

                    (instsVirtual, instSelState) <-
                      flip runStateT initialInstSelState
                        . flip
                          runReaderT
                          InstSelEnv
                            { varKinds = const (error "TODO: remove me?")
                            , nameTys = (ssaNameTypes HashMap.!)
                            , varTys = (varTypes HashMap.!)
                            }
                        $ traverse (instSelectionBlock instSelection_X86_64) ssa

                    pure (liveness, instsVirtual, instSelState)

                instsPhysical <-
                  flip evalStateT initialAllocRegistersState{stackFrameTop = instSelState.stackFrameTop}
                    . flip runReaderT AllocRegistersEnv{liveness}
                    $ traverse
                      ( \block ->
                          (\instructions' -> block{InstSelectionNew.instructions = instructions'})
                            <$> allocRegisters allocRegisters_X86_64 block.instructions
                      )
                      instsVirtual

                asm <-
                  runAsmBuilderT . handleLogging tempFileHandle $
                    traverse_ (\block -> Asm.block block.name [] Nothing (fmap Asm.Instruction block.instructions)) instsPhysical

                let asmText = printAsm (printInstruction_X86_64 printRegister) asm

                hClose tempFileHandle

                Builder.toLazyText asmText `shouldBe` Text.Lazy.unlines expectedOutput

        it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; f(x, y)" $
          ( Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
                Call Type.Uint64 (Name "f") [] [Var . F $ B (), Var $ B ()]
          )
            `shouldCompileTo` [ ".text"
                              , ".global main"
                              , "main:"
                              , "mov $1, %rax"
                              , "mov $2, %rbx"
                              , "call f"
                              ]

        it "f : Fn (Uint64, Uint64) Uint64 |- let x = 1; let y = 2; let z = f(x, y); x + z" $
          ( Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
                Let Type.Uint64 (Just "z") Type.Uint64 (Call Type.Uint64 (Name "f") [] [Var . F $ B (), Var $ B ()]) . toScope $
                  Add Type.Uint64 (Var . F . F $ B ()) (Var $ B ())
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
          ( Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
                Let Type.Uint64 (Just "z") Type.Uint64 (Call Type.Uint64 (Name "f") [] [Var $ B (), Var . F $ B ()]) . toScope $
                  Add Type.Uint64 (Var . F . F $ B ()) (Var $ B ())
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

      describe "functions" $ do
        let
          shouldCompileTo' :: (HasCallStack) => Seq (Register X86_64) -> Function -> [Lazy.Text] -> IO ()
          shouldCompileTo' available function expectedOutput =
            withSystemTempFile "metis-instruction-selection-logs.txt" $ \tempFilePath tempFileHandle ->
              saveLogsOnFailure tempFilePath $ do
                let nameTypes = [("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)]

                (liveness, instsVirtual, instSelState) <-
                  runVarT $ do
                    function' <- SSA.fromCoreFunction (nameTypes HashMap.!) function

                    let liveness = error "TODO: liveness for SSA"

                    let ssaNameTys = error "TODO: name types for SSA"

                    (instsVirtual, instSelState) <-
                      flip runStateT initialInstSelState
                        . flip
                          runReaderT
                          InstSelEnv
                            { varKinds = const (error "TODO: remove me?")
                            , nameTys = (ssaNameTys HashMap.!)
                            , varTys = (function'.varTypes HashMap.!)
                            }
                        $ instSelectionFunction instSelection_X86_64 function'

                    pure (liveness, instsVirtual, instSelState)

                instsPhysical <-
                  flip evalStateT initialAllocRegistersState{stackFrameTop = instSelState.stackFrameTop, freeRegisters = available}
                    . flip runReaderT AllocRegistersEnv{liveness}
                    $ allocRegistersFunction allocRegisters_X86_64 instsVirtual

                asm <-
                  runAsmBuilderT . handleLogging tempFileHandle $ do
                    _ <- Asm.block function.name [] Nothing []
                    traverse_
                      (\block -> Asm.block block.name [] Nothing (fmap Asm.Instruction block.instructions))
                      instsPhysical.blocks

                let asmText = printAsm (printInstruction_X86_64 printRegister) asm

                hClose tempFileHandle

                Builder.toLazyText asmText `shouldBe` Text.Lazy.unlines expectedOutput

          shouldCompileTo :: (HasCallStack) => Function -> [Lazy.Text] -> IO ()
          shouldCompileTo = shouldCompileTo' (generalPurposeRegisters @X86_64)

        it "f(x : Uint64, y : Uint64) : Uint64 = x + y" $
          Function
            { name = "f"
            , tyArgs = []
            , args = [("x", Type.Uint64), ("y", Type.Uint64)]
            , retTy = Type.Uint64
            , body = Add Type.Uint64 (Var 0) (Var 1)
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
            [Rax]
            Function
              { name = "f"
              , tyArgs = []
              , args = [("x", Type.Uint64), ("y", Type.Uint64)]
              , retTy = Type.Uint64
              , body = Add Type.Uint64 (Var 0) (Var 1)
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
            [Rax]
            Function
              { name = "f"
              , tyArgs = []
              , args = [("x", Type.Uint64), ("y", Type.Uint64), ("z", Type.Uint64)]
              , retTy = Type.Uint64
              , body = Add Type.Uint64 (Add Type.Uint64 (Var 0) (Var 1)) (Var 2)
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