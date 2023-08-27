{-# LANGUAGE DeriveTraversable #-}

module Metis.Core (
  Expr (..),
  typeOf,
  Definition (..),
) where

import Bound.Scope.Simple (Scope)
import Data.Text (Text)
import Data.Word (Word64)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.Type (Type)

data Expr a
  = Var a
  | Name Text
  | Literal Literal
  | Add Type (Expr a) (Expr a)
  | Subtract Type (Expr a) (Expr a)
  | Let Type (Maybe Text) Type (Expr a) (Scope () Expr a)
  | IfThenElse Type (Expr a) (Expr a) (Expr a)
  | Call Type (Expr a) [Expr a]
  deriving (Functor, Foldable, Traversable)

typeOf :: (Text -> Type) -> (a -> Type) -> Expr a -> Type
typeOf nameTy varTy expr =
  case expr of
    Var var -> varTy var
    Name name -> nameTy name
    Literal lit -> Literal.typeOf lit
    Add ty _ _ -> ty
    Subtract ty _ _ -> ty
    Let ty _ _ _ _ -> ty
    IfThenElse ty _ _ _ -> ty
    Call ty _ _ -> ty

data Definition = Function
  { name :: Text
  , args :: [(Text, Type)]
  , return :: Type
  , body :: Expr Word64
  }