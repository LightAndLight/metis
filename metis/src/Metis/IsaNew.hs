{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
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

data Address isa = Address {base :: AddressBase isa, offset :: Int64}
  deriving (Generic)

deriving instance (Isa isa) => Eq (Address isa)
deriving instance (Isa isa) => Show (Address isa)
instance (Isa isa) => Hashable (Address isa)

data AddressBase isa
  = BaseRegister (Register isa)
  | BaseLabel Symbol
  deriving (Generic)

deriving instance (Isa isa) => Eq (AddressBase isa)
deriving instance (Isa isa) => Show (AddressBase isa)
instance (Isa isa) => Hashable (AddressBase isa)

newtype Symbol = Symbol {value :: Text}
  deriving (Eq, Show, Hashable)