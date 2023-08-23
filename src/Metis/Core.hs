{-# LANGUAGE DeriveTraversable #-}

module Metis.Core (Expr (..), Compound (..), Simple (..), Type (..)) where

import Bound.Scope.Simple (Scope)
import Data.Text (Text)
import Metis.Literal (Literal)

data Simple a
  = SVar a
  | Literal Literal
  deriving (Functor, Foldable, Traversable)

data Compound a
  = Simple (Simple a)
  | Add (Simple a) (Simple a)
  | Subtract (Simple a) (Simple a)
  deriving (Functor, Foldable, Traversable)

data Expr a
  = Var a
  | Let (Maybe Text) Type (Compound a) (Scope () Expr a)
  deriving (Functor, Foldable, Traversable)

data Type
  = Int8
  | Int16
  | Int32
  | Int64
  | Uint8
  | Uint16
  | Uint32
  | Uint64