{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}

module Test.Anf (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.CallStack (HasCallStack)
import Data.Void (Void, absurd)
import qualified Metis.Anf as Anf
import Metis.Core (Expr (..), Function (..))
import qualified Metis.Kind as Kind
import qualified Metis.Literal as Literal
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.Anf" $ do
    describe "fromCore" $ do
      let
        anfShouldBe :: (HasCallStack) => Expr Void Void -> Anf.Expr -> IO ()
        anfShouldBe expr expectation = snd (Anf.fromCore absurd absurd expr) `shouldBe` expectation

      it "let x = 99; x + x" $ do
        let lit99 = Literal.Uint64 99

        let core =
              Let Type.Uint64 Nothing Type.Uint64 (Literal lit99) . toScope $
                Add Type.Uint64 (Var $ B ()) (Var $ B ())

        {-
        %0 = 99
        %1 = %0 + %0
        %1
        -}
        let anf =
              Anf.LetS
                (Anf.MkVar 0)
                (Anf.VarInfo{size = Type.sizeOf Type.Uint64})
                (Anf.Literal lit99)
                ( Anf.LetC
                    (Anf.MkVar 1)
                    (Anf.VarInfo{size = Type.sizeOf Type.Uint64})
                    (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 0) (Anf.Var $ Anf.MkVar 0))
                    (Anf.Return . Anf.Var $ Anf.MkVar 1)
                )

        core `anfShouldBe` anf
      it "let x = if true then 99 else 100; x + x" $ do
        let lit99 = Literal.Uint64 99
        let lit100 = Literal.Uint64 100

        let core =
              Let
                Type.Uint64
                Nothing
                Type.Uint64
                ( IfThenElse
                    Type.Uint64
                    (Literal $ Literal.Bool True)
                    (Literal lit99)
                    (Literal lit100)
                )
                . toScope
                $ Add Type.Uint64 (Var $ B ()) (Var $ B ())

        {-
        if true
          then jump @0(99)
          else jump @0(100)
        @0(%1):
        %2 = %1 + %1
        %2
        -}
        let anf =
              Anf.IfThenElse (Anf.Literal $ Literal.Bool True) (Anf.Jump (Anf.MkVar 0) (Anf.Literal lit99)) (Anf.Jump (Anf.MkVar 0) (Anf.Literal lit100)) $
                Anf.Label (Anf.MkVar 0) (Anf.MkVar 1) $
                  Anf.LetC (Anf.MkVar 2) (Anf.VarInfo{size = Type.sizeOf Type.Uint64}) (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 1) (Anf.Var $ Anf.MkVar 1)) $
                    Anf.Return (Anf.Var $ Anf.MkVar 2)

        core `anfShouldBe` anf
      it "let x = if true then let y = 1; y + 98 else let y = 2; let z = 3; y + z + 95; x + x" $ do
        let
          core =
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
        {-
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
        let uint64Info = Anf.VarInfo{size = 8}
        let anf =
              Anf.IfThenElse
                (Anf.Literal $ Literal.Bool True)
                ( Anf.LetS (Anf.MkVar 0) uint64Info (Anf.Literal $ Literal.Uint64 1) $
                    Anf.LetC (Anf.MkVar 1) uint64Info (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 0) (Anf.Literal $ Literal.Uint64 98)) $
                      Anf.Jump (Anf.MkVar 6) (Anf.Var $ Anf.MkVar 1)
                )
                ( Anf.LetS (Anf.MkVar 2) uint64Info (Anf.Literal $ Literal.Uint64 2) $
                    Anf.LetS (Anf.MkVar 3) uint64Info (Anf.Literal $ Literal.Uint64 3) $
                      Anf.LetC (Anf.MkVar 4) uint64Info (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 2) (Anf.Var $ Anf.MkVar 3)) $
                        Anf.LetC (Anf.MkVar 5) uint64Info (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 4) (Anf.Literal $ Literal.Uint64 95)) $
                          Anf.Jump (Anf.MkVar 6) (Anf.Var $ Anf.MkVar 5)
                )
                $ Anf.Label (Anf.MkVar 6) (Anf.MkVar 7)
                $ Anf.LetC (Anf.MkVar 8) uint64Info (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 7) (Anf.Var $ Anf.MkVar 7))
                $ Anf.Return (Anf.Var $ Anf.MkVar 8)

        core `anfShouldBe` anf
      it "let x = 1; let y = 2; 3 + f(x, y)" $ do
        let
          core =
            Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
                Add Type.Uint64 (Literal $ Literal.Uint64 3) (Call Type.Uint64 (Name "f") [] [Var . F $ B (), Var $ B ()])

        {-
        %0 = 1
        %1 = 2
        %2 = f(%0, %1)
        %3 = 3 + %2
        -}
        let uint64Info = Anf.VarInfo{size = 8}
        let anf =
              Anf.LetS (Anf.MkVar 0) uint64Info (Anf.Literal $ Literal.Uint64 1) $
                Anf.LetS (Anf.MkVar 1) uint64Info (Anf.Literal $ Literal.Uint64 2) $
                  Anf.LetC (Anf.MkVar 2) uint64Info (Anf.Call (Anf.Name "f") [Anf.Var $ Anf.MkVar 0, Anf.Var $ Anf.MkVar 1]) $
                    Anf.LetC (Anf.MkVar 3) uint64Info (Anf.Binop Anf.Add (Anf.Literal $ Literal.Uint64 3) (Anf.Var $ Anf.MkVar 2)) $
                      Anf.Return (Anf.Var $ Anf.MkVar 3)
        core `anfShouldBe` anf

      it "id : forall a. a -> a |- id @Uint64 99" $ do
        let core = Call Type.Uint64 (Name "id") [Type.Uint64] [Literal $ Literal.Uint64 99]

        let uint64Info = Anf.VarInfo{size = 8}
        let anf =
              Anf.LetC (Anf.MkVar 0) uint64Info (Anf.Call (Anf.Name "id") [Anf.Type Type.Uint64, Anf.Literal $ Literal.Uint64 99]) $
                Anf.Return (Anf.Var $ Anf.MkVar 0)
        core `anfShouldBe` anf

    describe "fromFunction" $ do
      let
        anfShouldBe :: (HasCallStack) => Function -> Anf.Function -> IO ()
        anfShouldBe function expectation = Anf.fromFunction function `shouldBe` expectation

      it "id @(a : Type) (x : a) = x" $ do
        Function
          { name = "id"
          , tyArgs = [("a", Kind.Type)]
          , args = [("x", Type.Var 0)]
          , retTy = Type.Var 0
          , body = Var 0
          }
          `anfShouldBe` Anf.Function
            { name = "id"
            , tyArgs = [(Anf.MkVar 0, Kind.Type)]
            , args = [(Anf.MkVar 1, Type.Var (Anf.MkVar 0))]
            , retTy = Type.Var (Anf.MkVar 0)
            , body = Anf.Return $ Anf.Var (Anf.MkVar 1)
            , bodyInfo =
                Anf.ExprInfo
                  { labelArgs = []
                  , varKinds = [(Anf.MkVar 0, Kind.Type)]
                  , varTys = [(Anf.MkVar 1, Type.Var (Anf.MkVar 0))]
                  }
            }