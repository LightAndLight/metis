module Metis.Literal (Literal (..), typeOf) where

import Data.Word (Word64)
import Metis.Type (Type)
import qualified Metis.Type as Type

data Literal
  = Uint64 Word64
  deriving (Show, Eq)

typeOf :: Literal -> Type
typeOf lit =
  case lit of
    Uint64{} -> Type.Uint64