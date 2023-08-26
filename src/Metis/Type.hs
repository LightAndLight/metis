module Metis.Type (Type (..), sizeOf) where

import Data.Word (Word64)

data Type
  = Uint64
  | Bool

sizeOf :: Type -> Word64
sizeOf ty =
  case ty of
    Uint64 -> 8
    Bool -> 1