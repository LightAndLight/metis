module Metis.Type (Type (..), sizeOf) where

import Data.Word (Word64)

data Type
  = Int8
  | Int16
  | Int32
  | Int64
  | Uint8
  | Uint16
  | Uint32
  | Uint64

sizeOf :: Type -> Word64
sizeOf ty =
  case ty of
    Int8 -> 1
    Int16 -> 2
    Int32 -> 4
    Int64 -> 8
    Uint8 -> 1
    Uint16 -> 2
    Uint32 -> 4
    Uint64 -> 8