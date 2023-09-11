module Metis.SSA (
  Instruction (..),
  Simple (..),
  typeOf,
  Compound (..),
  TypeDictField (..),
  typeDictFieldOffset,
  Binop (..),
  Terminator (..),
  Label (..),
) where

import Data.Int (Int64)
import Data.Text (Text)
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.SSA.Var (Var)
import Metis.Type (Type)
import qualified Metis.Type as Type

data Instruction
  = LetS Var (Type Var) Simple
  | LetC Var (Type Var) Compound

data Simple
  = Var Var
  | Name Text
  | Literal Literal
  | Type (Type Var)
  deriving (Show, Eq)

typeOf ::
  (Var -> Kind) ->
  (Text -> Type ty) ->
  (Var -> Type ty) ->
  Simple ->
  Either Kind (Type ty)
typeOf varKinds nameTys varTys simple =
  case simple of
    Var var -> Right $ varTys var
    Name name -> Right $ nameTys name
    Literal lit -> Right $ Literal.typeOf lit
    Type ty -> Left $ Type.kindOf varKinds ty

data Compound
  = Binop Binop Simple Simple
  | Call Simple [Var]
  | Alloca (Type Var)
  | Store Simple Simple
  | Load Simple
  | GetTypeDictField Simple TypeDictField
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

data Terminator
  = Return Simple
  | IfThenElse Simple (Label, Simple) (Label, Simple)
  | Jump Label Simple

newtype Label = Label Text