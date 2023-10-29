{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Test.LLVM (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO
import ErrorReporting (saveLogsOnFailure)
import LLVM.AST.Operand (Operand (..))
import LLVM.IRBuilder.Module (buildModule)
import LLVM.Pretty (ppllvm)
import Metis.Compile (ProgramError (..), ProgramResult (..), Stdin (..), Stdout (..), runProgram)
import qualified Metis.Core as Core
import qualified Metis.Kind as Kind
import Metis.LLVM (llvmFunction, llvmTypeDicts)
import qualified Metis.Literal as Literal
import qualified Metis.Type as Type
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)
import Test.Hspec (Spec, describe, expectationFailure, it)

shouldCompile :: Lazy.Text -> IO ()
shouldCompile moduleText =
  withSystemTempFile "testCompile.ll" $ \path handle -> saveLogsOnFailure path $ do
    Data.Text.Lazy.IO.hPutStrLn handle moduleText
    hClose handle
    result <- runProgram "llc" [path, "--filetype=null", "-o", "/dev/null"] NoStdin IgnoreStdout
    case result of
      Left err ->
        expectationFailure . unlines $
          [ "llc failed"
          , "exit code: " <> show err.status
          , "stdout: " <> Text.unpack err.stdout
          , "stderr: " <> Text.unpack err.stderr
          ]
      Right ProgramResult{stdout = ()} ->
        pure ()

spec :: Spec
spec =
  describe "Test.LLVM" $ do
    describe "llvmTypeDicts" $ do
      it "compiles" $ do
        let module_ = buildModule "test" llvmTypeDicts
        let moduleText = ppllvm module_
        shouldCompile moduleText

    describe "llvmFunction" $ do
      it "compiles `f x = 1 + (if x then 2 else 3)`" $ do
        let fn =
              Core.Function
                { name = "f"
                , tyArgs = []
                , args = [("x", Type.Bool)]
                , retTy = Type.Uint64
                , body =
                    Core.Add
                      Type.Uint64
                      (Core.Literal $ Literal.Uint64 1)
                      ( Core.IfThenElse
                          Type.Uint64
                          (Core.Var 0)
                          (Core.Literal $ Literal.Uint64 2)
                          (Core.Literal $ Literal.Uint64 3)
                      )
                }
        let module_ = buildModule "test" $ do
              typeDicts <- llvmTypeDicts
              llvmFunction (const undefined) typeDicts (const undefined) fn
        let moduleText = ppllvm module_
        shouldCompile moduleText

      it "compiles `id(type a, x : a) = a, f = 1 + id(Uint64, 2)`" $ do
        let id' =
              Core.Function
                { name = "id"
                , tyArgs = [("a", Kind.Type)]
                , args = [("x", Type.Var 0)]
                , retTy = Type.Var 0
                , body = Core.Var 0
                }
        let fn =
              Core.Function
                { name = "f"
                , tyArgs = []
                , args = []
                , retTy = Type.Uint64
                , body =
                    Core.Add
                      Type.Uint64
                      (Core.Literal $ Literal.Uint64 1)
                      ( Core.Call Type.Uint64 (Core.Name "id") [Type.Uint64] [Core.Literal $ Literal.Uint64 2]
                      )
                }
        let module_ = buildModule "test" $ do
              typeDicts <- llvmTypeDicts
              id'' <- llvmFunction (const undefined) typeDicts (const undefined) id'
              llvmFunction
                (\case "id" -> Type.Forall [("a", Kind.Type)] (toScope $ Type.Fn [Type.Var $ B 0] (Type.Var $ B 0)); _ -> undefined)
                typeDicts
                (\case "id" -> ConstantOperand id''; _ -> undefined)
                fn
        let moduleText = ppllvm module_
        shouldCompile moduleText