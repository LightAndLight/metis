{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}

module Test.CoreToAsm (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.Buildable (collectL')
import Data.CallStack (HasCallStack)
import Data.Foldable (for_, traverse_)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Text.Lazy as Text.Lazy
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Text.Lazy.Builder
import Data.Void (Void, absurd)
import ErrorReporting (saveLogsOnFailure)
import qualified Metis.Anf as Anf
import Metis.Asm (printAsm)
import Metis.Asm.Builder (runAsmBuilderT)
import Metis.Codegen (printInstruction_X86_64)
import Metis.Core (Expr (..), Function (..))
import Metis.InstSelection (instSelectionFunction_X86_64, instSelection_X86_64)
import Metis.Isa (generalPurposeRegisters)
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Kind as Kind
import qualified Metis.Literal as Literal
import qualified Metis.Liveness as Liveness
import Metis.Log (handleLogging)
import qualified Metis.Type as Type (Type (..), forall_)
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import qualified System.Process as Process
import Test.Hspec (Spec, SpecWith, describe, expectationFailure, it, shouldBe)

data TestCase where
  TestCase ::
    -- This call stack makes `hspec` report the call site of the `TestCase` on failure,
    -- instead of the location in `testCase` where the failure happened.
    (HasCallStack) =>
    { title :: String
    , definitions :: [Function]
    , expr :: Expr Void Void
    , availableRegisters :: Seq (Register X86_64)
    , expectedOutput :: [Builder]
    } ->
    TestCase

testCase :: TestCase -> SpecWith ()
testCase TestCase{title, definitions, expr, availableRegisters, expectedOutput} =
  it title . withSystemTempFile "metis-coretoasm-logs.txt" $ \tempFilePath tempFileHandle -> saveLogsOnFailure tempFilePath $ do
    asm <- fmap (Text.Lazy.Builder.toLazyText . printAsm printInstruction_X86_64) . runAsmBuilderT . handleLogging tempFileHandle $ do
      let nameTysMap =
            collectL' @(HashMap _ _) $
              fmap (\Function{name, tyArgs, args, retTy} -> (name, Type.forall_ tyArgs $ Type.Fn (fmap snd args) retTy)) definitions
      let nameTys name = Maybe.fromMaybe (error $ show name <> " missing from name types map") $ HashMap.lookup name nameTysMap

      for_ definitions $ \function -> do
        let function' = Anf.fromFunction function
        let liveness = Liveness.liveness function'.body
        instSelectionFunction_X86_64 nameTys availableRegisters liveness function'

      _ <- do
        let (anfInfo, anf) = Anf.fromCore absurd absurd expr
        let liveness = Liveness.liveness anf
        instSelection_X86_64
          nameTys
          availableRegisters
          anfInfo
          anf
          liveness
          "main"
          []

      pure ()
    hClose tempFileHandle
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
        , definitions = []
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
        , definitions = []
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
        , definitions = []
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
        , definitions = []
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
        , definitions = []
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
        , definitions = []
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
        , definitions = []
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
    , TestCase
        { title = "fn f(x : Uint64, y : Uint64) : Uint64 = x + y; fn main() = let x = 1; let y = 2; 3 + f(x, y)"
        , definitions =
            [ Function
                { name = "f"
                , tyArgs = []
                , args = [("x", Type.Uint64), ("y", Type.Uint64)]
                , retTy = Type.Uint64
                , body =
                    Add
                      Type.Uint64
                      (Var 0)
                      (Var 1)
                }
            ]
        , expr =
            Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
                Add Type.Uint64 (Literal $ Literal.Uint64 3) (Call Type.Uint64 (Name "f") [] [Var . F $ B (), Var $ B ()])
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ ".text"
            , "f:"
            , -- `x` is in `rax`
              -- `y` is in `rbx`
              "add %rbx, %rax"
            , "pop %rbp"
            , "ret"
            , {-
              %0 = 1
              %1 = 2
              %2 = f(%0, %1)
              %3 = 3 + %2
              -}
              "main:"
            , "mov $1, %rax"
            , "mov $2, %rbx"
            , "push $after"
            , "push %rbp"
            , "mov %rsp, %rbp"
            , "jmp f"
            , "after:"
            , "mov $3, %rbx"
            , "add %rax, %rbx"
            ]
        }
    , TestCase
        { title = "fn f(x : Uint64, y : Uint64) : Uint64 = x + y; fn main() = let x = 1; let y = 2; x + f(x, y)"
        , definitions =
            [ Function
                { name = "f"
                , tyArgs = []
                , args = [("x", Type.Uint64), ("y", Type.Uint64)]
                , retTy = Type.Uint64
                , body =
                    Add
                      Type.Uint64
                      (Var 0)
                      (Var 1)
                }
            ]
        , expr =
            Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
                Add Type.Uint64 (Var . F $ B ()) (Call Type.Uint64 (Name "f") [] [Var . F $ B (), Var $ B ()])
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ ".text"
            , "f:"
            , -- `x` is in `rax`
              -- `y` is in `rbx`
              "add %rbx, %rax"
            , "pop %rbp"
            , "ret"
            , {-
              %0 = 1
              %1 = 2
              %2 = f(%0, %1)
              %3 = %0 + %2
              -}
              "main:"
            , "mov $1, %rax"
            , "mov $2, %rbx"
            , "push %rax"
            , "push $after"
            , "push %rbp"
            , "mov %rsp, %rbp"
            , "jmp f"
            , "after:"
            , "mov %rax, %rbx"
            , "pop %rax"
            , "add %rbx, %rax"
            ]
        }
    , TestCase
        { title = "fn id @(a : Type) (x : a) : a = x; fn main() = let x = id @Uint64 99; x + 1"
        , definitions =
            [ Function
                { name = "id"
                , tyArgs = [("a", Kind.Type)]
                , args = [("x", Type.Var 0)]
                , retTy = Type.Var 0
                , body = Var 0
                }
            ]
        , expr =
            Let Type.Uint64 (Just "x") Type.Uint64 (Call Type.Uint64 (Name "id") [Type.Uint64] [Literal $ Literal.Uint64 99]) . toScope $
              Var (B ())
        , availableRegisters = generalPurposeRegisters @X86_64
        , expectedOutput =
            [ ".data"
            , -- begin: Uint64 type dictionary
              "type_Uint64:"
            , ".quad 8"
            , ".quad Type_Uint64_copy"
            , -- end: Uint64 type dictionary
              ".text"
            , -- begin: Uint64 copy
              "Type_Uint64_copy:"
            , -- rax: self
              -- rbx: from (pointer)
              -- rcx: to (pointer)
              "mov (%rbx), %rdx"
            , "mov %rdx, (%rcx)"
            , -- return
              "pop %rbp"
            , "ret"
            , -- end: Uint64 copy
              "id:" -- (a : Type, x : a) -> a
            , {-
              id(%a : *Type, %x : *Unknown):
              %0 = copy(%a, %x)
              ret %0
              -}
              -- `a : Type` is in `rax`
              -- `x : a` is in `rbx`
              -- result destination is in `rcx`
              "mov 8(%rax), %rdx" -- load the `copy` function pointer
              -- begin: call `copy`
            , "push $after"
            , "push %rbp"
            , "mov %rsp, %rbp"
            , "jmp *%rdx"
            , -- end: call `copy`
              "after:"
            , -- return
              -- return value is already in `rax`
              "pop %rbp"
            , "ret"
            , {-
              %0 = alloca(Uint64)
              store(%0, 99)
              %1 = f(&type_Uint64, %0)
              %2 = load(%0)
              %3 = %2 + 1
              %3
              -}
              "main:"
            , "mov %rsp, %rbp"
            , "sub $16, %rsp" -- allocate locals
            , "mov $99, -8(%rbp)"
            , -- set up arguments
              "lea type_Uint64, %rax" -- address of Uint64 type dictionary
            , "lea -8(%rbp), %rbx" -- argument passed via stack
            , "lea -16(%rbp), %rcx" -- result passed via stack
            , -- begin: call `id`
              "push $after"
            , "push %rbp"
            , "mov %rsp, %rbp"
            , "jmp id"
            , -- end: call `id`
              "after:"
            , "add $1, (%rax)"
            ]
        }
    ]