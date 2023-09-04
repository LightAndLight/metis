{-# LANGUAGE OverloadedLists #-}

module Test.Liveness (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.CallStack (HasCallStack)
import Data.HashMap.Strict (HashMap)
import Data.Void (Void, absurd)
import qualified Metis.Anf as Anf
import Metis.Core (Expr (..))
import qualified Metis.Literal as Literal
import Metis.Liveness (Liveness (..))
import qualified Metis.Liveness as Liveness
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.Liveness" $ do
    let
      livenessShouldBe :: (HasCallStack) => Expr Void Void -> HashMap Anf.Var Liveness -> IO ()
      livenessShouldBe expr expectation = do
        let (_info, anf) = Anf.fromCore absurd absurd expr
        let liveness = Liveness.liveness anf

        liveness `shouldBe` expectation
    it "let x = 99; x + x" $ do
      let
        expr =
          let
            lit99 = Literal $ Literal.Uint64 99
           in
            Let Type.Uint64 Nothing Type.Uint64 lit99 . toScope $
              Add Type.Uint64 (Var $ B ()) (Var $ B ())

      expr
        `livenessShouldBe` [ (Anf.MkVar 0, Liveness{kills = []})
                           , (Anf.MkVar 1, Liveness{kills = [Anf.MkVar 0]})
                           ]
    it "let x = if true then let y = 1; y + 98 else let y = 2; let z = 3; y + z + 95; x + x" $ do
      let
        expr =
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

      expr
        `livenessShouldBe` [ (Anf.MkVar 0, Liveness{kills = []})
                           , (Anf.MkVar 1, Liveness{kills = [Anf.MkVar 0]})
                           , (Anf.MkVar 2, Liveness{kills = []})
                           , (Anf.MkVar 3, Liveness{kills = []})
                           , (Anf.MkVar 4, Liveness{kills = [Anf.MkVar 2, Anf.MkVar 3]})
                           , (Anf.MkVar 5, Liveness{kills = [Anf.MkVar 4]})
                           , (Anf.MkVar 7, Liveness{kills = [Anf.MkVar 1, Anf.MkVar 5]})
                           , (Anf.MkVar 8, Liveness{kills = [Anf.MkVar 7]})
                           ]
    it "let x = 1; let y = if true then x else 22; x + y" $ do
      let
        expr =
          let
            lit1 = Literal $ Literal.Uint64 1
            lit22 = Literal $ Literal.Uint64 22
            value = IfThenElse Type.Uint64 (Literal $ Literal.Bool True) (Var $ B ()) lit22
           in
            Let Type.Uint64 (Just "x") Type.Uint64 lit1 . toScope $
              Let Type.Uint64 (Just "y") Type.Uint64 value . toScope $
                Add Type.Uint64 (Var $ F $ B ()) (Var $ B ())
      {-
      %0 = 1
      if true
        then jump @1 %0
        else jump @1 22
      @1(%2):
      %3 = %0 + %2
      %3
      -}

      expr
        `livenessShouldBe` [ (Anf.MkVar 0, Liveness{kills = []})
                           , (Anf.MkVar 2, Liveness{kills = []})
                           , (Anf.MkVar 3, Liveness{kills = [Anf.MkVar 0, Anf.MkVar 2]})
                           ]
    it "let x = 1; let y = 2; let z = f(y, x); x + z" $ do
      let
        expr =
          Let Type.Uint64 (Just "x") Type.Uint64 (Literal $ Literal.Uint64 1) . toScope $
            Let Type.Uint64 (Just "y") Type.Uint64 (Literal $ Literal.Uint64 2) . toScope $
              Let Type.Uint64 (Just "z") Type.Uint64 (Call Type.Uint64 (Name "f") [] [Var $ B (), Var . F $ B ()]) . toScope $
                Add Type.Uint64 (Var . F . F $ B ()) (Var $ B ())

      {-
      %0 = 1
      %1 = 2
      %2 = f(%1, %0)
      %3 = %0 + %2
      -}

      expr
        `livenessShouldBe` [ (Anf.MkVar 0, Liveness{kills = []})
                           , (Anf.MkVar 1, Liveness{kills = []})
                           , (Anf.MkVar 2, Liveness{kills = [Anf.MkVar 1]})
                           , (Anf.MkVar 3, Liveness{kills = [Anf.MkVar 0, Anf.MkVar 2]})
                           ]