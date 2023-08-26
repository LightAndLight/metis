{-# LANGUAGE DeriveTraversable #-}

module Metis.Core (
  Expr (..),
  typeOf,
) where

import Bound.Scope.Simple (Scope)
import Data.Text (Text)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.Type (Type)

data Expr a
  = Var a
  | Literal Literal
  | Add Type (Expr a) (Expr a)
  | Subtract Type (Expr a) (Expr a)
  | Let Type (Maybe Text) Type (Expr a) (Scope () Expr a)
  | IfThenElse Type (Expr a) (Expr a) (Expr a)
  deriving (Functor, Foldable, Traversable)

typeOf :: (a -> Type) -> Expr a -> Type
typeOf varTy expr =
  case expr of
    Var var -> varTy var
    Literal lit -> Literal.typeOf lit
    Add ty _ _ -> ty
    Subtract ty _ _ -> ty
    Let ty _ _ _ _ -> ty
    IfThenElse ty _ _ _ -> ty