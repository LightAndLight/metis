{-# LANGUAGE OverloadedLists #-}

module Test.Anf (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.CallStack (HasCallStack)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import Data.Void (Void, absurd)
import qualified Metis.Anf as Anf
import Metis.Core (Expr (..), Function (..))
import qualified Metis.Kind as Kind
import qualified Metis.Literal as Literal
import Metis.Type (Type)
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.Anf" $ do
    describe "fromCore" $ do
      let
        anfShouldBe :: (HasCallStack) => (HashMap Text (Type Anf.Var), Expr Void Void) -> Anf.Expr -> IO ()
        anfShouldBe (nameTys, expr) expectation = snd (Anf.fromCore (nameTys HashMap.!) absurd absurd expr) `shouldBe` expectation

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
                Type.Uint64
                (Anf.Literal lit99)
                ( Anf.LetC
                    (Anf.MkVar 1)
                    Type.Uint64
                    (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 0) (Anf.Var $ Anf.MkVar 0))
                    (Anf.Return . Anf.Var $ Anf.MkVar 1)
                )

        (mempty, core) `anfShouldBe` anf

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
                  Anf.LetC (Anf.MkVar 2) Type.Uint64 (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 1) (Anf.Var $ Anf.MkVar 1)) $
                    Anf.Return (Anf.Var $ Anf.MkVar 2)

        (mempty, core) `anfShouldBe` anf
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
        let anf =
              Anf.IfThenElse
                (Anf.Literal $ Literal.Bool True)
                ( Anf.LetS (Anf.MkVar 0) Type.Uint64 (Anf.Literal $ Literal.Uint64 1) $
                    Anf.LetC (Anf.MkVar 1) Type.Uint64 (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 0) (Anf.Literal $ Literal.Uint64 98)) $
                      Anf.Jump (Anf.MkVar 6) (Anf.Var $ Anf.MkVar 1)
                )
                ( Anf.LetS (Anf.MkVar 2) Type.Uint64 (Anf.Literal $ Literal.Uint64 2) $
                    Anf.LetS (Anf.MkVar 3) Type.Uint64 (Anf.Literal $ Literal.Uint64 3) $
                      Anf.LetC (Anf.MkVar 4) Type.Uint64 (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 2) (Anf.Var $ Anf.MkVar 3)) $
                        Anf.LetC (Anf.MkVar 5) Type.Uint64 (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 4) (Anf.Literal $ Literal.Uint64 95)) $
                          Anf.Jump (Anf.MkVar 6) (Anf.Var $ Anf.MkVar 5)
                )
                $ Anf.Label (Anf.MkVar 6) (Anf.MkVar 7)
                $ Anf.LetC (Anf.MkVar 8) Type.Uint64 (Anf.Binop Anf.Add (Anf.Var $ Anf.MkVar 7) (Anf.Var $ Anf.MkVar 7))
                $ Anf.Return (Anf.Var $ Anf.MkVar 8)

        (mempty, core) `anfShouldBe` anf
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
        let anf =
              Anf.LetS (Anf.MkVar 0) Type.Uint64 (Anf.Literal $ Literal.Uint64 1) $
                Anf.LetS (Anf.MkVar 1) Type.Uint64 (Anf.Literal $ Literal.Uint64 2) $
                  Anf.LetC (Anf.MkVar 2) Type.Uint64 (Anf.Call (Anf.Name "f") [Anf.Var $ Anf.MkVar 0, Anf.Var $ Anf.MkVar 1]) $
                    Anf.LetC (Anf.MkVar 3) Type.Uint64 (Anf.Binop Anf.Add (Anf.Literal $ Literal.Uint64 3) (Anf.Var $ Anf.MkVar 2)) $
                      Anf.Return (Anf.Var $ Anf.MkVar 3)
        ([("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)], core) `anfShouldBe` anf

      it "id : forall a. a -> a |- id @Uint64 99" $ do
        let core = Call Type.Uint64 (Name "id") [Type.Uint64] [Literal $ Literal.Uint64 99]

        {-
        %0 : *Uint64 = alloca(Uint64)
        %1 : ()      = store(%0, 99)
        %2 : *Uint64 = alloca(Uint64)
        %3 : *Uint64 = id(Uint64, %0, %2)
        %4 : Uint64  = load(%3)
        ret %4
        -}
        let anf =
              Anf.LetC (Anf.MkVar 0) (Type.Ptr Type.Uint64) (Anf.Alloca Type.Uint64) $
                Anf.LetC (Anf.MkVar 1) Type.Unit (Anf.Store (Anf.Var $ Anf.MkVar 0) (Anf.Literal $ Literal.Uint64 99)) $
                  Anf.LetC (Anf.MkVar 2) (Type.Ptr Type.Uint64) (Anf.Alloca Type.Uint64) $
                    Anf.LetC (Anf.MkVar 3) (Type.Ptr Type.Uint64) (Anf.Call (Anf.Name "id") [Anf.Type Type.Uint64, Anf.Var $ Anf.MkVar 0, Anf.Var $ Anf.MkVar 2]) $
                      Anf.LetC (Anf.MkVar 4) Type.Uint64 (Anf.Load (Anf.Var $ Anf.MkVar 3)) $
                        Anf.Return (Anf.Var $ Anf.MkVar 4)
        ( [("id", Type.Forall [("a", Kind.Type)] . toScope $ Type.Fn [Type.Var $ B 0] (Type.Var $ B 0))]
          , core
          )
          `anfShouldBe` anf

    describe "fromFunction" $ do
      let
        anfShouldBe :: (HasCallStack) => Function -> Anf.Function -> IO ()
        anfShouldBe function expectation = Anf.fromFunction (const undefined) function `shouldBe` expectation

      it "id @(a : Type) (x : a) : a = x" $ do
        Function
          { name = "id"
          , tyArgs = [("a", Kind.Type)]
          , args = [("x", Type.Var 0)]
          , retTy = Type.Var 0
          , body = Var 0
          }
          `anfShouldBe` Anf.Function
            { name = "id"
            , args =
                [ (Anf.MkVar 0, Type.Ptr Type.Unknown)
                , (Anf.MkVar 1, Type.Ptr $ Type.Var (Anf.MkVar 0))
                , (Anf.MkVar 2, Type.Ptr $ Type.Var (Anf.MkVar 0))
                ]
            , retTy = Type.Ptr $ Type.Var (Anf.MkVar 0)
            , body =
                {-
                %0 : *Type
                %1 : *%0
                %2 : *%0
                ---
                %3 : (*Type = %0, *%0) -> *%0 = %0.move
                %4 : *%0 = %3(%0, %1, %2)
                ret %4
                -}
                Anf.LetC
                  (Anf.MkVar 3)
                  (Type.Fn [Type.Ptr Type.Unknown, Type.Ptr $ Type.Var (Anf.MkVar 0), Type.Ptr $ Type.Var (Anf.MkVar 0)] (Type.Ptr $ Type.Var (Anf.MkVar 0)))
                  (Anf.GetTypeDictField (Anf.Var $ Anf.MkVar 0) Anf.TypeDictMove)
                  $ Anf.LetC
                    (Anf.MkVar 4)
                    (Type.Ptr $ Type.Var (Anf.MkVar 0))
                    ( Anf.Call
                        (Anf.Var $ Anf.MkVar 3)
                        [Anf.Var $ Anf.MkVar 0, Anf.Var $ Anf.MkVar 1, Anf.Var $ Anf.MkVar 2]
                    )
                  $ Anf.Return (Anf.Var $ Anf.MkVar 4)
            , bodyInfo =
                Anf.ExprInfo
                  { labelArgs = []
                  , varKinds = [(Anf.MkVar 0, Kind.Type)]
                  , varTys =
                      [ (Anf.MkVar 1, Type.Ptr $ Type.Var (Anf.MkVar 0))
                      , (Anf.MkVar 2, Type.Ptr $ Type.Var (Anf.MkVar 0))
                      ,
                        ( Anf.MkVar 3
                        , Type.Fn
                            [Type.Ptr Type.Unknown, Type.Ptr $ Type.Var (Anf.MkVar 0), Type.Ptr $ Type.Var (Anf.MkVar 0)]
                            (Type.Ptr $ Type.Var (Anf.MkVar 0))
                        )
                      , (Anf.MkVar 4, Type.Ptr $ Type.Var (Anf.MkVar 0))
                      ]
                  }
            }