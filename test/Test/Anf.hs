module Test.Anf (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Data.Void (absurd)
import qualified Metis.Anf as Anf
import Metis.Core (Expr (..))
import qualified Metis.Literal as Literal
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.Anf" $ do
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
                  (Anf.Simple . Anf.Var $ Anf.MkVar 1)
              )

      Anf.fromCore absurd core `shouldBe` anf