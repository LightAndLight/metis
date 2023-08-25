{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}

module Test.CoreToAsm (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.CallStack (HasCallStack)
import Data.Foldable (traverse_)
import Data.Sequence (Seq)
import qualified Data.Text.Lazy as Text.Lazy
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Text.Lazy.Builder
import Data.Void (Void, absurd)
import Metis.AllocateRegisters (allocateRegisters_X86_64)
import qualified Metis.Anf as Anf
import Metis.Codegen (printInstructions_X86_64)
import Metis.Core (Expr (..))
import Metis.Isa (Isa (generalPurposeRegisters))
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Literal as Literal
import qualified Metis.Liveness as Liveness
import Metis.Log (noLogging)
import qualified Metis.Type as Type (Type (..))
import System.Exit (ExitCode (..))
import qualified System.Process as Process
import Test.Hspec (Spec, SpecWith, describe, expectationFailure, it, shouldBe)

data TestCase where
  TestCase ::
    -- This call stack makes `hspec` report the call site of the `TestCase` on failure,
    -- instead of the location in `testCase` where the failure happened.
    (HasCallStack) =>
    { title :: String
    , expr :: Expr Void
    , availableRegisters :: Seq (Register X86_64)
    , expectedOutput :: [Builder]
    } ->
    TestCase

testCase :: TestCase -> SpecWith ()
testCase TestCase{title, expr, availableRegisters, expectedOutput} =
  it title $ do
    let anf = Anf.fromCore absurd expr
    let liveness = Liveness.liveness anf
    (insts, _) <- noLogging $ allocateRegisters_X86_64 availableRegisters anf liveness
    let asm = Text.Lazy.Builder.toLazyText (printInstructions_X86_64 insts)
    asm `shouldBe` Text.Lazy.Builder.toLazyText (foldMap @[] (<> "\n") expectedOutput)

    (exitCode, stdout, stderr) <- Process.readProcessWithExitCode "as" ["-o", "/dev/null"] (Text.Lazy.unpack asm)
    case exitCode of
      ExitSuccess -> pure ()
      ExitFailure code ->
        expectationFailure $
          "`as` exited with status "
            <> show code
            <> "\nstdout:\n"
            <> stdout
            <> "\nstderr:\n"
            <> stderr

spec :: Spec
spec =
  describe "Test.CoreToAsm" . traverse_ @[] testCase $
    [ TestCase
        { title = "99 + 99"
        , expr =
            let
              lit99 = Literal $ Literal.Uint64 99
             in
              Let Type.Uint64 Nothing Type.Uint64 (Add Type.Uint64 lit99 lit99) . toScope $
                Var (B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ "mov $99, %rax"
            , "add $99, %rax"
            ]
        }
    , TestCase
        { title = "let x = 99; x + x"
        , expr =
            let
              lit99 = Literal $ Literal.Uint64 99
             in
              Let Type.Uint64 Nothing Type.Uint64 lit99 . toScope $
                Add Type.Uint64 (Var $ B ()) (Var $ B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ "mov $99, %rax"
            , "add %rax, %rax"
            ]
        }
    , TestCase
        { title = "let x = 99; let y = 100; x + y"
        , expr =
            let
              lit99 = Literal $ Literal.Uint64 99
              lit100 = Literal $ Literal.Uint64 100
             in
              Let Type.Uint64 Nothing Type.Uint64 lit99 . toScope $
                Let Type.Uint64 Nothing Type.Uint64 lit100 . toScope $
                  Add Type.Uint64 (Var $ F $ B ()) (Var $ B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ "mov $99, %rax"
            , "mov $100, %rbx"
            , "add %rbx, %rax"
            ]
        }
    , TestCase
        { title = "let x = 99; let y = 100; let z = 101; x + y + z"
        , expr =
            let
              lit99 = Literal $ Literal.Uint64 99
              lit100 = Literal $ Literal.Uint64 100
              lit101 = Literal $ Literal.Uint64 101
             in
              Let Type.Uint64 Nothing Type.Uint64 lit99 . toScope $
                Let Type.Uint64 Nothing Type.Uint64 lit100 . toScope $
                  Let Type.Uint64 Nothing Type.Uint64 lit101 . toScope $
                    Add Type.Uint64 (Add Type.Uint64 (Var . F . F $ B ()) (Var . F $ B ())) (Var $ B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ "mov $99, %rax"
            , "mov $100, %rbx"
            , "mov $101, %rcx"
            , "add %rbx, %rax"
            , "add %rcx, %rax"
            ]
        }
    , TestCase
        { title = "let x = 99; let y = 100; let z = 101; x + y + z (only %rax)"
        , expr =
            let
              lit99 = Literal $ Literal.Uint64 99
              lit100 = Literal $ Literal.Uint64 100
              lit101 = Literal $ Literal.Uint64 101
             in
              Let Type.Uint64 Nothing Type.Uint64 lit99 . toScope $
                Let Type.Uint64 Nothing Type.Uint64 lit100 . toScope $
                  Let Type.Uint64 Nothing Type.Uint64 lit101 . toScope $
                    Add Type.Uint64 (Add Type.Uint64 (Var . F . F $ B ()) (Var . F $ B ())) (Var $ B ())
        , availableRegisters = [Rax]
        , expectedOutput =
            [ "mov $99, %rax"
            , "mov $100, 0(%rbp)"
            , "mov $101, -8(%rbp)"
            , "add 0(%rbp), %rax"
            , "add -8(%rbp), %rax"
            ]
        }
    ]