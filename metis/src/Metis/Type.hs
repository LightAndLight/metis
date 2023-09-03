{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Metis.Type (
  Type (..),
  sizeOf,
  pointerSize,
  CallingConvention (..),
  callingConventionOf,
  kindOf,
) where

import Data.Hashable (Hashable)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Metis.Kind (Kind)
import qualified Metis.Kind as Kind

data Type a
  = Var a
  | Uint64
  | Bool
  | Fn [Type a] (Type a)
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

instance (Hashable a) => Hashable (Type a)

pointerSize :: Word64
pointerSize = 8 -- assumes 64 bit target architecture

sizeOf :: Type a -> Word64
sizeOf ty =
  case ty of
    Var{} -> pointerSize
    Uint64 -> 8
    Bool -> 1
    Fn{} -> pointerSize

data CallingConvention
  = Register
  | Composite [CallingConvention]

callingConventionOf :: Type a -> CallingConvention
callingConventionOf ty =
  case ty of
    Var{} -> Register
    Uint64 -> Register
    Bool -> Register
    Fn{} -> Register

kindOf :: (a -> Kind) -> Type a -> Kind
kindOf varKind ty =
  case ty of
    Var a -> varKind a
    Uint64 -> Kind.Type
    Bool -> Kind.Type
    Fn{} -> Kind.Type