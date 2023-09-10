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
  Memory (..),
  MemoryBase (..),
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

data Memory isa = Mem {base :: MemoryBase isa, offset :: Int64}
  deriving (Generic)

deriving instance (Eq (Register isa)) => Eq (Memory isa)
deriving instance (Show (Register isa)) => Show (Memory isa)
instance (Hashable (Register isa)) => Hashable (Memory isa)

data MemoryBase isa
  = BaseRegister (Register isa)
  | BaseLabel Symbol
  deriving (Generic)

deriving instance (Eq (Register isa)) => Eq (MemoryBase isa)
deriving instance (Show (Register isa)) => Show (MemoryBase isa)
instance (Hashable (Register isa)) => Hashable (MemoryBase isa)

newtype Symbol = Symbol {value :: Text}
  deriving (Eq, Show, Hashable)