module Metis.Type (
  Type (..),
  sizeOf,
  pointerSize,
  CallingConvention (..),
  callingConventionOf,
) where

import Data.Word (Word64)

data Type
  = Uint64
  | Bool
  | Fn [Type] Type
  deriving (Show, Eq)

pointerSize :: Word64
pointerSize = 8 -- assumes 64 bit target architecture

sizeOf :: Type -> Word64
sizeOf ty =
  case ty of
    Uint64 -> 8
    Bool -> 1
    Fn{} -> pointerSize

data CallingConvention
  = Register
  | Composite [CallingConvention]

callingConventionOf :: Type -> CallingConvention
callingConventionOf ty =
  case ty of
    Uint64 -> Register
    Bool -> Register
    Fn{} -> Register