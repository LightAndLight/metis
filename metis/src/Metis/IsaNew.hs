{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Metis.IsaNew (
  Isa (..),
  Immediate (..),
  sizeOfImmediate,
  Address (..),
  AddressBase (..),
  addOffset,
  Symbol (..),
) where

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
  , Traversable (Instruction isa)
  , forall var. (Eq var) => Eq (Instruction isa var)
  , forall var. (Show var) => Show (Instruction isa var)
  ) =>
  Isa isa
  where
  data Register isa :: Type
  data Instruction isa :: Type -> Type

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

data Address var = Address {base :: AddressBase var, offset :: Int64}
  deriving (Functor, Foldable, Traversable, Generic)

deriving instance (Eq var) => Eq (Address var)
deriving instance (Show var) => Show (Address var)
instance (Hashable var) => Hashable (Address var)

data AddressBase var
  = BaseVar var
  | BaseLabel Symbol
  deriving (Functor, Foldable, Traversable, Generic)

deriving instance (Eq var) => Eq (AddressBase var)
deriving instance (Show var) => Show (AddressBase var)
instance (Hashable var) => Hashable (AddressBase var)

addOffset :: Address var -> Int64 -> Address var
addOffset addr offset = addr{offset = addr.offset + offset}

newtype Symbol = Symbol {value :: Text}
  deriving (Eq, Show, Hashable)