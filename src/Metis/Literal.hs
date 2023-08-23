module Metis.Literal (Literal (..), typeOf) where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Word (Word16, Word32, Word64, Word8)
import Metis.Type (Type)
import qualified Metis.Type as Type

data Literal
  = Int8 Int8
  | Int16 Int16
  | Int32 Int32
  | Int64 Int64
  | Uint8 Word8
  | Uint16 Word16
  | Uint32 Word32
  | Uint64 Word64

typeOf :: Literal -> Type
typeOf lit =
  case lit of
    Int8{} -> Type.Int8
    Int16{} -> Type.Int16
    Int32{} -> Type.Int32
    Int64{} -> Type.Int64
    Uint8{} -> Type.Uint8
    Uint16{} -> Type.Uint16
    Uint32{} -> Type.Uint32
    Uint64{} -> Type.Uint64