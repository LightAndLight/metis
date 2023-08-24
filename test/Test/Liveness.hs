{-# LANGUAGE OverloadedLists #-}

module Test.Liveness (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.Void (absurd)
import qualified Metis.Anf as Anf
import Metis.Core (Compound (..), Expr (..), Simple (..))
import qualified Metis.Literal as Literal
import Metis.Liveness (Liveness (..))
import qualified Metis.Liveness as Liveness
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.Liveness" $ do
    it "let x = 99; x + x" $ do
      let
        expr =
          let
            lit99 = Literal $ Literal.Uint64 99
           in
            LetS Nothing Type.Uint64 lit99 . toScope $
              LetC Nothing Type.Uint64 (Add (Var $ B ()) (Var $ B ())) . toScope $
                Simple (Var $ B ())
      let anf = Anf.fromCore absurd expr
      let liveness = Liveness.liveness anf

      liveness
        `shouldBe` [ (Anf.MkVar 0, Liveness{kills = []})
                   , (Anf.MkVar 1, Liveness{kills = [Anf.MkVar 0]})
                   ]