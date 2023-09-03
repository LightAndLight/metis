{-# LANGUAGE DeriveTraversable #-}

module Metis.Core (
  Expr (..),
  typeOf,
  Function (..),
) where

import Bound.Scope.Simple (Scope)
import Data.Text (Text)
import Data.Word (Word64)
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.Type (Type)

data Expr ty tm
  = Var tm
  | Name Text
  | Literal Literal
  | Add (Type ty) (Expr ty tm) (Expr ty tm)
  | Subtract (Type ty) (Expr ty tm) (Expr ty tm)
  | Let (Type ty) (Maybe Text) (Type ty) (Expr ty tm) (Scope () (Expr ty) tm)
  | IfThenElse (Type ty) (Expr ty tm) (Expr ty tm) (Expr ty tm)
  | Call (Type ty) (Expr ty tm) [Type ty] [Expr ty tm]
  deriving (Functor, Foldable, Traversable)

typeOf :: (Text -> Type ty) -> (tm -> Type ty) -> Expr ty tm -> Type ty
typeOf nameTy varTy expr =
  case expr of
    Var var -> varTy var
    Name name -> nameTy name
    Literal lit -> Literal.typeOf lit
    Add ty _ _ -> ty
    Subtract ty _ _ -> ty
    Let ty _ _ _ _ -> ty
    IfThenElse ty _ _ _ -> ty
    Call ty _ _ _ -> ty

data Function = Function
  { name :: Text
  , tyArgs :: [(Text, Kind)]
  , args :: [(Text, Type Word64)]
  , retTy :: Type Word64
  , body :: Expr Word64 Word64
  }