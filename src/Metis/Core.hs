{-# LANGUAGE DeriveTraversable #-}

module Metis.Core (
  Expr (..),
  Compound (..),
  Simple (..),
) where

import Bound.Scope.Simple (Scope)
import Data.Text (Text)
import Metis.Literal (Literal)
import Metis.Type (Type)

data Simple a
  = Var a
  | Literal Literal
  deriving (Functor, Foldable, Traversable)

data Compound a
  = Add (Simple a) (Simple a)
  | Subtract (Simple a) (Simple a)
  deriving (Functor, Foldable, Traversable)

data Expr a
  = Simple (Simple a)
  | LetS (Maybe Text) Type (Simple a) (Scope () Expr a)
  | LetC (Maybe Text) Type (Compound a) (Scope () Expr a)
  deriving (Functor, Foldable, Traversable)