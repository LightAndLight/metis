{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeApplications #-}

module Test.CoreToAsm (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.Foldable (traverse_)
import Data.Sequence (Seq)
import qualified Data.Text.Lazy as Text.Lazy
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Text.Lazy.Builder
import Data.Void (Void, absurd)
import Metis.AllocateRegisters (allocateRegisters_X86_64)
import Metis.Codegen (printInstructions_X86_64)
import Metis.Core (Compound (..), Expr (..), Simple (..))
import qualified Metis.Core as Type (Type (..))
import Metis.Isa (Isa (generalPurposeRegisters))
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Literal as Literal
import qualified Metis.SSA as SSA
import System.Exit (ExitCode (..))
import qualified System.Process as Process
import Test.Hspec (Spec, SpecWith, describe, expectationFailure, it, shouldBe)

data TestCase = TestCase
  { title :: String
  , expr :: Expr Void
  , availableRegisters :: Seq (Register X86_64)
  , expectedOutput :: [Builder]
  }

testCase :: TestCase -> SpecWith ()
testCase TestCase{title, expr, availableRegisters, expectedOutput} =
  it title $ do
    let ssa = SSA.fromCore 0 absurd expr
    let (insts, _) = allocateRegisters_X86_64 availableRegisters ssa
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
              Let Nothing Type.Uint64 (Add lit99 lit99) . toScope $
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
              Let Nothing Type.Uint64 (Simple lit99) . toScope $
                Let Nothing Type.Uint64 (Add (SVar $ B ()) (SVar $ B ())) . toScope $
                  Var (B ())
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
              Let Nothing Type.Uint64 (Simple lit99) . toScope $
                Let Nothing Type.Uint64 (Simple lit100) . toScope $
                  Let Nothing Type.Uint64 (Add (SVar $ F $ B ()) (SVar $ B ())) . toScope $
                    Var (B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ "mov $99, %rbx"
            , "mov $100, %rax"
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
              Let Nothing Type.Uint64 (Simple lit99) . toScope $
                Let Nothing Type.Uint64 (Simple lit100) . toScope $
                  Let Nothing Type.Uint64 (Simple lit101) . toScope $
                    Let Nothing Type.Uint64 (Add (SVar $ F $ F $ B ()) (SVar $ F $ B ())) . toScope $
                      Let Nothing Type.Uint64 (Add (SVar $ B ()) (SVar $ F $ B ())) . toScope $
                        Var (B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , {-
          %0 = 99
          %1 = 100
          %2 = 101
          %3 = %0 + %1
          %4 = %3 + %2

          {%2 -> %rax, %3 -> %rbx}
          %rax = %rbx + %rax

          {%0 -> %rcx, %1 -> %rbx, %2 -> %rax}
          %rbx = %rcx + %rbx
          %rax = %rbx + %rax

          {%0 -> %rcx, %1 -> %rbx}
          %rax = 101
          %rbx = %rcx + %rbx
          %rax = %rbx + %rax

          {%0 -> %rcx}
          %rbx = 100
          %rax = 101
          %rbx = %rcx + %rbx
          %rax = %rbx + %rax

          %rcx = 99
          %rbx = 100
          %rax = 101
          %rbx = %rcx + %rbx
          %rax = %rbx + %rax
          -}
          expectedOutput =
            [ "mov $99, %rcx"
            , "mov $100, %rbx"
            , "mov $101, %rax"
            , "add %rcx, %rbx"
            , "add %rbx, %rax"
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
              Let Nothing Type.Uint64 (Simple lit99) . toScope $
                Let Nothing Type.Uint64 (Simple lit100) . toScope $
                  Let Nothing Type.Uint64 (Simple lit101) . toScope $
                    Let Nothing Type.Uint64 (Add (SVar $ F $ F $ B ()) (SVar $ F $ B ())) . toScope $
                      Let Nothing Type.Uint64 (Add (SVar $ B ()) (SVar $ F $ B ())) . toScope $
                        Var (B ())
        , availableRegisters = [Rax]
        , {-
          %0 = 99
          %1 = 100
          %2 = 101
          %3 = %0 + %1
          %4 = %3 + %2

          {%2 -> %rax, %3 -> 0(%rbp)}
          %rax = 0(%rbp) + %rax

          {%0 -> -8(%rbp), %1 -> 0(%rbp), %2 -> %rax}
          0(%rbp) = -8(%rbp) + 0(%rbp)
          %rax = 0(%rbp) + %rax

          {%0 -> -8(%rbp), %1 -> 0(%rbp)}
          %rax = 101
          0(%rbp) = -8(%rbp) + 0(%rbp)
          %rax = 0(%rbp) + %rax

          {%0 -> -8(%rbp)}
          0(%rbp) = 100
          %rax = 101
          0(%rbp) = -8(%rbp) + 0(%rbp)
          %rax = 0(%rbp) + %rax

          {}
          -8(%rbp) = 99
          0(%rbp) = 100
          %rax = 101
          0(%rbp) = -8(%rbp) + 0(%rbp)
          %rax = 0(%rbp) + %rax

          {}
          -8(%rbp) = 99
          0(%rbp) = 100
          %rax = 101
          push %rax
          %rax = -8(%rbp)
          0(%rbp) = %rax + 0(%rbp)
          pop %rax
          %rax = 0(%rbp) + %rax
          -}
          expectedOutput =
            [ "mov $99, -8(%rbp)"
            , "mov $100, 0(%rbp)"
            , "mov $101, %rax"
            , "push %rax"
            , "mov -8(%rbp), %rax"
            , "add %rax, 0(%rbp)"
            , "pop %rax"
            , "add 0(%rbp), %rax"
            ]
        }
    ]