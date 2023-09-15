{-# LANGUAGE OverloadedLists #-}

module Test.LivenessNew (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.CallStack (HasCallStack)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import Data.Void (Void, absurd)
import Metis.Core (Expr (..))
import qualified Metis.Literal as Literal
import Metis.LivenessNew (Liveness (..), livenessBlocks, runLivenessT)
import qualified Metis.SSA as SSA
import Metis.SSA.Var (runVarT)
import qualified Metis.SSA.Var as SSA (unsafeVar)
import Metis.Type (Type)
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.LivenessNew" $ do
    let
      livenessShouldBe :: (HasCallStack) => (HashMap Text (Type Void), Expr Void Void) -> Liveness -> IO ()
      livenessShouldBe (nameTypes, expr) expectation = do
        (_varTypes, ssa) <-
          runVarT . SSA.toBlocks SSA.FromCoreEnv{nameTypes = (nameTypes HashMap.!)} "main" $
            SSA.fromCoreExpr absurd absurd expr
        (liveness, _) <- runLivenessT $ livenessBlocks ssa

        liveness `shouldBe` expectation

    it "let x = 99; x + x" $ do
      let
        expr =
          let
            lit99 = Literal $ Literal.Uint64 99
           in
            Let Type.Uint64 Nothing Type.Uint64 lit99 . toScope $
              Add Type.Uint64 (Var $ B ()) (Var $ B ())

      (mempty, expr)
        `livenessShouldBe` (mempty :: Liveness){varKills = [(SSA.unsafeVar 1, [SSA.unsafeVar 0])]}
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
      ifThenElse true @then @else
      @then:
      %0 = 1
      %1 = %0 + 98
      jump @after %1
      @else:
      %2 = 2
      %3 = 3
      %4 = %2 + %3
      %5 = %4 + 95
      jump @after %5
      @after(%6):
      %7 = %6 + %6
      return %7
      -}

      (mempty, expr)
        `livenessShouldBe` (mempty :: Liveness)
          { varKills =
              [ (SSA.unsafeVar 1, [SSA.unsafeVar 0])
              , (SSA.unsafeVar 4, [SSA.unsafeVar 2, SSA.unsafeVar 3])
              , (SSA.unsafeVar 5, [SSA.unsafeVar 4])
              , (SSA.unsafeVar 7, [SSA.unsafeVar 6])
              ]
          , labelKills =
              [(SSA.Label "after", [SSA.unsafeVar 1, SSA.unsafeVar 5])]
          }

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
      ifThenElse true @then @else
      @then:
      jump @after %0
      @else:
      jump @after 22
      @after(%1):
      %2 = %0 + %1
      return %2
      -}

      (mempty, expr)
        `livenessShouldBe` (mempty :: Liveness)
          { varKills =
              [ (SSA.unsafeVar 2, [SSA.unsafeVar 0, SSA.unsafeVar 1])
              ]
          }

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

      ([("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)], expr)
        `livenessShouldBe` (mempty :: Liveness)
          { varKills =
              [ (SSA.unsafeVar 2, [SSA.unsafeVar 1])
              , (SSA.unsafeVar 3, [SSA.unsafeVar 0, SSA.unsafeVar 2])
              ]
          }