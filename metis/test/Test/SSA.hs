{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Test.SSA (spec) where

import Bound.Scope.Simple (toScope)
import Bound.Var (Var (..))
import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (runStateT)
import Data.CallStack (HasCallStack)
import qualified Data.DList as DList
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import Data.Void (Void, absurd)
import Metis.Core (Expr (..))
import qualified Metis.Kind as Kind
import qualified Metis.Literal as Literal
import qualified Metis.SSA as SSA
import Metis.SSA.Var (runVarT)
import qualified Metis.SSA.Var as SSA (unsafeVar)
import Metis.Type (Type)
import qualified Metis.Type as Type
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.SSA" $ do
    describe "fromCoreExpr" $ do
      let
        ssaShouldBe :: (HasCallStack) => (HashMap Text (Type Void), Expr Void Void) -> [SSA.Block] -> IO ()
        ssaShouldBe (nameTypes, expr) expectation = do
          (simple, s) <-
            runVarT
              . flip runStateT SSA.initialFromCoreState
              . flip runReaderT SSA.FromCoreEnv{nameTypes = (nameTypes HashMap.!)}
              $ SSA.fromCoreExpr absurd absurd expr
          let blocks =
                DList.snoc
                  s.previousBlocks
                  SSA.Block
                    { name = s.currentName
                    , params = s.currentParams
                    , instructions = DList.toList s.currentInstructions
                    , terminator = SSA.Return simple
                    }
          DList.toList blocks `shouldBe` expectation

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
        let ssa =
              [ SSA.Block
                  { name = "unnamed"
                  , params = []
                  , instructions =
                      [ SSA.LetS (SSA.unsafeVar 0) Type.Uint64 (SSA.Literal lit99)
                      , SSA.LetC (SSA.unsafeVar 1) Type.Uint64 (SSA.Binop SSA.Add (SSA.Var $ SSA.unsafeVar 0) (SSA.Var $ SSA.unsafeVar 0))
                      ]
                  , terminator =
                      SSA.Return . SSA.Var $ SSA.unsafeVar 1
                  }
              ]

        (mempty, core) `ssaShouldBe` ssa

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
        ifthenelse true @then @else
        @then:
        jump @after(99)
        @else:
        jump @after(100)
        @after(%0)
        %1 = %0 + %0
        ret %1
        -}
        let ssa =
              [ SSA.Block
                  { name = "unnamed"
                  , params = []
                  , instructions = []
                  , terminator = SSA.IfThenElse (SSA.Literal $ Literal.Bool True) (SSA.Label "then") (SSA.Label "else")
                  }
              , SSA.Block
                  { name = "then"
                  , params = []
                  , instructions = []
                  , terminator = SSA.Jump (SSA.Label "after") (SSA.Literal lit99)
                  }
              , SSA.Block
                  { name = "else"
                  , params = []
                  , instructions = []
                  , terminator = SSA.Jump (SSA.Label "after") (SSA.Literal lit100)
                  }
              , SSA.Block
                  { name = "after"
                  , params = [SSA.unsafeVar 0]
                  , instructions =
                      [ SSA.LetC (SSA.unsafeVar 1) Type.Uint64 (SSA.Binop SSA.Add (SSA.Var $ SSA.unsafeVar 0) (SSA.Var $ SSA.unsafeVar 0))
                      ]
                  , terminator =
                      SSA.Return (SSA.Var $ SSA.unsafeVar 1)
                  }
              ]

        (mempty, core) `ssaShouldBe` ssa
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
        if true @then @else
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
        let ssa =
              [ SSA.Block
                  { name = "unnamed"
                  , params = []
                  , instructions = []
                  , terminator = SSA.IfThenElse (SSA.Literal $ Literal.Bool True) (SSA.Label "then") (SSA.Label "else")
                  }
              , SSA.Block
                  { name = "then"
                  , params = []
                  , instructions =
                      [ SSA.LetS (SSA.unsafeVar 0) Type.Uint64 (SSA.Literal $ Literal.Uint64 1)
                      , SSA.LetC (SSA.unsafeVar 1) Type.Uint64 (SSA.Binop SSA.Add (SSA.Var $ SSA.unsafeVar 0) (SSA.Literal $ Literal.Uint64 98))
                      ]
                  , terminator = SSA.Jump (SSA.Label "after") (SSA.Var $ SSA.unsafeVar 1)
                  }
              , SSA.Block
                  { name = "else"
                  , params = []
                  , instructions =
                      [ SSA.LetS (SSA.unsafeVar 2) Type.Uint64 (SSA.Literal $ Literal.Uint64 2)
                      , SSA.LetS (SSA.unsafeVar 3) Type.Uint64 (SSA.Literal $ Literal.Uint64 3)
                      , SSA.LetC (SSA.unsafeVar 4) Type.Uint64 (SSA.Binop SSA.Add (SSA.Var $ SSA.unsafeVar 2) (SSA.Var $ SSA.unsafeVar 3))
                      , SSA.LetC (SSA.unsafeVar 5) Type.Uint64 (SSA.Binop SSA.Add (SSA.Var $ SSA.unsafeVar 4) (SSA.Literal $ Literal.Uint64 95))
                      ]
                  , terminator = SSA.Jump (SSA.Label "after") (SSA.Var $ SSA.unsafeVar 5)
                  }
              , SSA.Block
                  { name = "after"
                  , params = [SSA.unsafeVar 6]
                  , instructions =
                      [ SSA.LetC (SSA.unsafeVar 7) Type.Uint64 (SSA.Binop SSA.Add (SSA.Var $ SSA.unsafeVar 6) (SSA.Var $ SSA.unsafeVar 6))
                      ]
                  , terminator = SSA.Return . SSA.Var $ SSA.unsafeVar 7
                  }
              ]

        (mempty, core) `ssaShouldBe` ssa
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
        let ssa =
              [ SSA.Block
                  { name = "unnamed"
                  , params = []
                  , instructions =
                      [ SSA.LetS (SSA.unsafeVar 0) Type.Uint64 (SSA.Literal $ Literal.Uint64 1)
                      , SSA.LetS (SSA.unsafeVar 1) Type.Uint64 (SSA.Literal $ Literal.Uint64 2)
                      , SSA.LetC (SSA.unsafeVar 2) Type.Uint64 (SSA.Call (SSA.Name "f") [SSA.unsafeVar 0, SSA.unsafeVar 1])
                      , SSA.LetC (SSA.unsafeVar 3) Type.Uint64 (SSA.Binop SSA.Add (SSA.Literal $ Literal.Uint64 3) (SSA.Var $ SSA.unsafeVar 2))
                      ]
                  , terminator = SSA.Return (SSA.Var $ SSA.unsafeVar 3)
                  }
              ]
        ([("f", Type.Fn [Type.Uint64, Type.Uint64] Type.Uint64)], core) `ssaShouldBe` ssa

      it "id : forall a. a -> a |- id @Uint64 99" $ do
        let core = Call Type.Uint64 (Name "id") [Type.Uint64] [Literal $ Literal.Uint64 99]

        {-
        %0 : *Unknown = Uint64
        %1 : *Uint64  = alloca(Uint64)
        %2 : ()       = store(%1, 99)
        %3 : *Uint64  = alloca(Uint64)
        %4 : *Uint64  = id(%0, %1, %3)
        %5 : Uint64   = load(%4)
        return %5
        -}
        let ssa =
              [ SSA.Block
                  { name = "unnamed"
                  , params = []
                  , instructions =
                      [ SSA.LetS (SSA.unsafeVar 0) (Type.Ptr Type.Unknown) (SSA.Type Type.Uint64)
                      , SSA.LetC (SSA.unsafeVar 1) (Type.Ptr Type.Uint64) (SSA.Alloca Type.Uint64)
                      , SSA.LetC (SSA.unsafeVar 2) Type.Unit (SSA.Store (SSA.Var $ SSA.unsafeVar 1) (SSA.Literal $ Literal.Uint64 99))
                      , SSA.LetC (SSA.unsafeVar 3) (Type.Ptr Type.Uint64) (SSA.Alloca Type.Uint64)
                      , SSA.LetC (SSA.unsafeVar 4) (Type.Ptr Type.Uint64) (SSA.Call (SSA.Name "id") [SSA.unsafeVar 0, SSA.unsafeVar 1, SSA.unsafeVar 3])
                      , SSA.LetC (SSA.unsafeVar 5) Type.Uint64 (SSA.Load (SSA.Var $ SSA.unsafeVar 4))
                      ]
                  , terminator = SSA.Return (SSA.Var $ SSA.unsafeVar 5)
                  }
              ]
        ( [("id", Type.Forall [("a", Kind.Type)] . toScope $ Type.Fn [Type.Var $ B 0] (Type.Var $ B 0))]
          , core
          )
          `ssaShouldBe` ssa

{-
describe "fromFunction" $ do
  let
    ssaShouldBe :: (HasCallStack) => Function -> SSA.Function -> IO ()
    ssaShouldBe function expectation = SSA.fromFunction (const undefined) function `shouldBe` expectation

  it "id @(a : Type) (x : a) : a = x" $ do
    Function
      { name = "id"
      , tyArgs = [("a", Kind.Type)]
      , args = [("x", Type.Var 0)]
      , retTy = Type.Var 0
      , body = Var 0
      }
      `ssaShouldBe` SSA.Function
        { name = "id"
        , args =
            [ (SSA.unsafeVar 0, Type.Ptr Type.Unknown)
            , (SSA.unsafeVar 1, Type.Ptr $ Type.Var (SSA.unsafeVar 0))
            , (SSA.unsafeVar 2, Type.Ptr $ Type.Var (SSA.unsafeVar 0))
            ]
        , retTy = Type.Ptr $ Type.Var (SSA.unsafeVar 0)
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
            SSA.LetC
              (SSA.unsafeVar 3)
              (Type.Fn [Type.Ptr Type.Unknown, Type.Ptr $ Type.Var (SSA.unsafeVar 0), Type.Ptr $ Type.Var (SSA.unsafeVar 0)] (Type.Ptr $ Type.Var (SSA.unsafeVar 0)))
              (SSA.GetTypeDictField (SSA.Var $ SSA.unsafeVar 0) SSA.TypeDictMove)
              $ SSA.LetC
                (SSA.unsafeVar 4)
                (Type.Ptr $ Type.Var (SSA.unsafeVar 0))
                ( SSA.Call
                    (SSA.Var $ SSA.unsafeVar 3)
                    [SSA.Var $ SSA.unsafeVar 0, SSA.Var $ SSA.unsafeVar 1, SSA.Var $ SSA.unsafeVar 2]
                )
              $ SSA.Return (SSA.Var $ SSA.unsafeVar 4)
        , bodyInfo =
            SSA.ExprInfo
              { labelArgs = []
              , varKinds = [(SSA.unsafeVar 0, Kind.Type)]
              , varTys =
                  [ (SSA.unsafeVar 1, Type.Ptr $ Type.Var (SSA.unsafeVar 0))
                  , (SSA.unsafeVar 2, Type.Ptr $ Type.Var (SSA.unsafeVar 0))
                  ,
                    ( SSA.unsafeVar 3
                    , Type.Fn
                        [Type.Ptr Type.Unknown, Type.Ptr $ Type.Var (SSA.unsafeVar 0), Type.Ptr $ Type.Var (SSA.unsafeVar 0)]
                        (Type.Ptr $ Type.Var (SSA.unsafeVar 0))
                    )
                  , (SSA.unsafeVar 4, Type.Ptr $ Type.Var (SSA.unsafeVar 0))
                  ]
              }
        }
-}