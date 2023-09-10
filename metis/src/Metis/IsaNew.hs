{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Metis.IsaNew (
  Isa (..),
  Immediate (..),
  sizeOfImmediate,
  Address (..),
  AddressBase (..),
  addOffset,
  traverseVarsAddress,
  mapVarsAddress,
  Symbol (..),
) where

import Data.Functor.Identity (Identity (..))
import Data.Hashable (Hashable)
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Generics (Generic)

class
  ( Eq (Register isa)
  , Show (Register isa)
  , Hashable (Register isa)
  , forall var. (forall a. (Eq a) => Eq (var a)) => Eq (Instruction isa var)
  , forall var. (forall a. (Show a) => Show (var a)) => Show (Instruction isa var)
  ) =>
  Isa isa
  where
  data Register isa :: Type
  data Instruction isa :: (Type -> Type) -> Type

  registerSize :: Register isa -> Word64
  pointerSize :: Word64

  framePointerRegister :: Register isa

  registerName :: Register isa -> Text

  generalPurposeRegisters :: Seq (Register isa)

data Immediate
  = Word64 Word64
  | Label Symbol
  deriving (Eq, Show)

sizeOfImmediate :: forall isa. (Isa isa) => Immediate -> Word64
sizeOfImmediate i =
  case i of
    Word64{} -> 8
    Label{} -> pointerSize @isa

data Address isa var = Address {base :: AddressBase isa var, offset :: Int64}
  deriving (Generic)

deriving instance (Isa isa, forall a. (Eq a) => Eq (var a)) => Eq (Address isa var)
deriving instance (Isa isa, forall a. (Show a) => Show (var a)) => Show (Address isa var)
instance (Isa isa, forall a. (Eq a) => Eq (var a), forall a. (Hashable a) => Hashable (var a)) => Hashable (Address isa var)

data AddressBase isa var
  = BaseVar (var (Register isa))
  | BaseLabel Symbol
  deriving (Generic)

deriving instance (Isa isa, forall a. (Eq a) => Eq (var a)) => Eq (AddressBase isa var)
deriving instance (Isa isa, forall a. (Show a) => Show (var a)) => Show (AddressBase isa var)
instance (Isa isa, forall a. (Eq a) => Eq (var a), forall a. (Hashable a) => Hashable (var a)) => Hashable (AddressBase isa var)

addOffset :: Address isa var -> Int64 -> Address isa var
addOffset addr offset = addr{offset = addr.offset + offset}

traverseVarsAddress ::
  (Applicative m) =>
  (forall a. (a ~ Register isa) => var a -> m (var' a)) ->
  Address isa var ->
  m (Address isa var')
traverseVarsAddress f addr =
  case addr.base of
    BaseVar var ->
      (\var' -> Address{base = BaseVar var', offset = addr.offset}) <$> f var
    BaseLabel l ->
      pure $ Address{base = BaseLabel l, offset = addr.offset}

mapVarsAddress ::
  (forall a. var a -> var' a) ->
  Address isa var ->
  Address isa var'
mapVarsAddress f = runIdentity . traverseVarsAddress (Identity . f)

newtype Symbol = Symbol {value :: Text}
  deriving (Eq, Show, Hashable)