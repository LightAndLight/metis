module Metis.SSA (
  Instruction (..),
  Simple (..),
  Compound (..),
  TypeDictField (..),
  typeDictFieldOffset,
  Binop (..),
  Terminator (..),
  Label (..),
) where

import Data.Int (Int64)
import Data.Text (Text)
import Metis.IsaNew (Register)
import Metis.Literal (Literal)
import Metis.SSA.Var (AnyVar, Var)
import Metis.Type (Type)

data Instruction isa
  = LetS (Var (Register isa)) (Type AnyVar) (Simple isa)
  | LetC (Var (Register isa)) (Type AnyVar) (Compound isa)

data Simple isa
  = Var (Var (Register isa))
  | Name Text
  | Literal Literal
  | Type (Type AnyVar)
  deriving (Show, Eq)

data Compound isa
  = Binop Binop (Simple isa) (Simple isa)
  | Call (Simple isa) [Simple isa]
  | Alloca (Type AnyVar)
  | Store (Simple isa) (Simple isa)
  | Load (Simple isa)
  | GetTypeDictField (Simple isa) TypeDictField
  deriving (Show, Eq)

data TypeDictField
  = TypeDictSize
  | TypeDictMove
  deriving (Show, Eq)

typeDictFieldOffset :: TypeDictField -> Int64
typeDictFieldOffset field =
  case field of
    TypeDictSize -> 0
    TypeDictMove -> 8

data Binop = Add | Subtract
  deriving (Show, Eq)

data Terminator isa
  = Return (Simple isa)
  | IfThenElse (Simple isa) (Label, Simple isa) (Label, Simple isa)
  | Jump Label (Simple isa)

newtype Label = Label Text