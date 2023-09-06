{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Metis.Type (
  Type (..),
  forall_,
  sizeOf,
  pointerSize,
  CallingConvention (..),
  callingConventionOf,
  kindOf,
) where

import Bound.Class ((>>>=))
import Bound.Scope.Simple (Scope, toScope)
import Bound.Var (Var (..))
import qualified Control.Monad
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Hashable (Hashable, hashWithSalt)
import Data.Hashable.Lifted (Hashable1, hashWithSalt1)
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Generics (Generic, Generic1)
import GHC.Stack (HasCallStack)
import Metis.Kind (Kind)
import qualified Metis.Kind as Kind

data Type a
  = Var a
  | Uint64
  | Bool
  | Fn [Type a] (Type a)
  | Forall [(Text, Kind)] (Scope Word64 Type a)
  | Ptr (Type a)
  | Unit
  | Unknown
  deriving (Functor, Foldable, Traversable, Generic, Generic1)

deriveShow1 ''Type
deriveEq1 ''Type

instance (Eq a) => Eq (Type a) where (==) = eq1
instance (Show a) => Show (Type a) where showsPrec = showsPrec1
instance Hashable1 Type
instance (Hashable a) => Hashable (Type a) where hashWithSalt = hashWithSalt1

instance Applicative Type where
  pure = Var
  (<*>) = Control.Monad.ap

instance Monad Type where
  Var a >>= f = f a
  Uint64 >>= _ = Uint64
  Bool >>= _ = Bool
  Unit >>= _ = Unit
  Unknown >>= _ = Unknown
  Fn args ret >>= f = Fn (fmap (>>= f) args) (ret >>= f)
  Forall args body >>= f = Forall args (body >>>= f)
  Ptr a >>= f = Ptr (a >>= f)

pointerSize :: Word64
pointerSize = 8 -- assumes 64 bit target architecture

sizeOf :: (HasCallStack) => Type a -> Word64
sizeOf ty =
  case ty of
    Var{} -> pointerSize
    Uint64 -> 8
    Bool -> 1
    Fn{} -> pointerSize
    Forall{} -> pointerSize
    Ptr{} -> pointerSize
    Unit -> 0
    Unknown -> error "can't get size of Unknown"

data CallingConvention
  = Register
  | Composite [CallingConvention]
  | Erased

callingConventionOf :: (HasCallStack) => Type a -> CallingConvention
callingConventionOf ty =
  case ty of
    Var{} -> Register
    Uint64 -> Register
    Bool -> Register
    Fn{} -> Register
    Forall{} -> Register
    Ptr{} -> Register
    Unit -> Erased
    Unknown -> error "can't get calling convention of Unknown"

kindOf :: (a -> Kind) -> Type a -> Kind
kindOf varKind ty =
  case ty of
    Var a -> varKind a
    Uint64 -> Kind.Type
    Bool -> Kind.Type
    Fn{} -> Kind.Type
    Forall{} -> Kind.Type
    Ptr{} -> Kind.Type
    Unit -> Kind.Type
    Unknown -> Kind.Type

forall_ :: [(Text, Kind)] -> Type Word64 -> Type a
forall_ tyVars body =
  case tyVars of
    [] ->
      case traverse (const Nothing) body of
        Nothing -> error $ "type variable found in " <> show body
        Just body' -> body'
    _ -> Forall tyVars . toScope $ fmap B body