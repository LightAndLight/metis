module Metis.Literal (Literal (..), typeOf) where

import Data.Word (Word64)
import Metis.Type (Type)
import qualified Metis.Type as Type

data Literal
  = Uint64 Word64
  | Bool Bool
  deriving (Show, Eq)

typeOf :: Literal -> Type a
typeOf lit =
  case lit of
    Uint64{} -> Type.Uint64
    Bool{} -> Type.Bool