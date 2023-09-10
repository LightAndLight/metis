module Metis.SSA (
  Instruction (..),
  Simple (..),
  Compound (..),
  TypeDictField (..),
  Binop (..),
  Terminator (..),
  Label (..),
) where

import Data.Text (Text)
import Metis.IsaNew (Register)
import Metis.Literal (Literal)
import Metis.SSA.Var (AnyVar, Var)
import Metis.Type (Type)

data Instruction isa
  = LetS (Var (Register isa)) (Type AnyVar) Simple
  | LetC (Var (Register isa)) (Type AnyVar) Compound

data Simple
  = Var AnyVar
  | Name Text
  | Literal Literal
  | Type (Type AnyVar)
  deriving (Show, Eq)

data Compound
  = Binop Binop Simple Simple
  | Call Simple [Simple]
  | Alloca (Type AnyVar)
  | Store Simple Simple
  | Load Simple
  | GetTypeDictField Simple TypeDictField
  deriving (Show, Eq)

data TypeDictField
  = TypeDictSize
  | TypeDictMove
  deriving (Show, Eq)

data Binop = Add | Subtract
  deriving (Show, Eq)

data Terminator
  = Return Simple
  | IfThenElse Simple (Label, Simple) (Label, Simple)
  | Jump Label Simple

newtype Label = Label Text