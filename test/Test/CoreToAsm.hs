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
import qualified Metis.Anf as Anf
import Metis.Asm (printAsm)
import Metis.Asm.Builder (runAsmBuilderT)
import Metis.Codegen (printInstruction_X86_64)
import Metis.Core (Expr (..))
import Metis.InstSelection (instSelection_X86_64)
import Metis.Isa (generalPurposeRegisters)
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
    let (anfInfo, anf) = Anf.fromCore absurd expr
    let liveness = Liveness.liveness anf
    asm <- fmap (Text.Lazy.Builder.toLazyText . printAsm printInstruction_X86_64) . runAsmBuilderT . noLogging $ do
      let nameTys = const undefined
      _ <- instSelection_X86_64 nameTys availableRegisters anfInfo anf liveness "main" []
      pure ()
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
            [ ".text"
            , "main:"
            , "mov $99, %rax"
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
            [ ".text"
            , "main:"
            , "mov $99, %rax"
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
            [ ".text"
            , "main:"
            , "mov $99, %rax"
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
            [ ".text"
            , "main:"
            , "mov $99, %rax"
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
            [ ".text"
            , "main:"
            , "mov $99, %rax"
            , "mov $100, -8(%rbp)"
            , "mov $101, -16(%rbp)"
            , "add -8(%rbp), %rax"
            , "add -16(%rbp), %rax"
            ]
        }
    , TestCase
        { title = "let x = if true then let y = 1; y + 98 else let y = 2; let z = 3; y + z + 95; x + x"
        , expr =
            let
              lit98 = Literal $ Literal.Uint64 98
              lit1 = Literal $ Literal.Uint64 1
              lit2 = Literal $ Literal.Uint64 2
              lit3 = Literal $ Literal.Uint64 3
              lit95 = Literal $ Literal.Uint64 95
              value =
                IfThenElse
                  Type.Uint64
                  (Literal $ Literal.Bool True)
                  ( Let Type.Uint64 (Just "y") Type.Uint64 lit1 . toScope $
                      Add Type.Uint64 (Var $ B ()) lit98
                  )
                  ( Let Type.Uint64 (Just "y") Type.Uint64 lit2 . toScope $
                      Let Type.Uint64 (Just "z") Type.Uint64 lit3 . toScope $
                        Add Type.Uint64 (Add Type.Uint64 (Var . F $ B ()) (Var $ B ())) lit95
                  )
             in
              Let Type.Uint64 (Just "x") Type.Uint64 value . toScope $
                Add Type.Uint64 (Var $ B ()) (Var $ B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , {-
          if true
            then
              %0 = 1
              %1 = %0 + 98
              jump @6 %1
            else
              %2 = 2
              %3 = 3
              %4 = %2 + %3
              %5 = %4 + 95
              jump @6 %5
          @6(%7):
          %8 = %7 + %7
          %8
          -}
          expectedOutput =
            [ ".text"
            , "main:"
            , "mov $1, %rax"
            , "cmp $0, %rax"
            , "je else"
            , "then:"
            , "mov $1, %rax"
            , "add $98, %rax"
            , "jmp block_6"
            , "else:"
            , "mov $2, %rax"
            , "mov $3, %rbx"
            , "add %rbx, %rax"
            , "add $95, %rax"
            , "jmp block_6"
            , "block_6:"
            , "add %rax, %rax"
            ]
        }
    , TestCase
        { title = "let x = 3; let y = if true then x else 22; x + y"
        , expr =
            let
              lit3 = Literal $ Literal.Uint64 3
              lit22 = Literal $ Literal.Uint64 22
              value = IfThenElse Type.Uint64 (Literal $ Literal.Bool True) (Var $ B ()) lit22
             in
              Let Type.Uint64 (Just "x") Type.Uint64 lit3 . toScope $
                Let Type.Uint64 (Just "y") Type.Uint64 value . toScope $
                  Add Type.Uint64 (Var $ F $ B ()) (Var $ B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            {-
            %0 = 3
            if true
              then jump @1 %0
              else jump @1 22
            @1(%2):
            %3 = %0 + %2
            %3
            -}
            [ ".text"
            , "main:"
            , "mov $3, %rax"
            , "mov $1, %rbx"
            , "cmp $0, %rbx"
            , "je else"
            , "then:"
            , "mov %rax, %rbx"
            , "jmp block_1"
            , "else:"
            , "mov $22, %rbx"
            , "jmp block_1"
            , "block_1:"
            , "add %rbx, %rax"
            ]
        }
    ]