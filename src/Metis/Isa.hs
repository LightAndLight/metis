{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Metis.Isa (
  Isa (..),
  Immediate (..),
  ToImmediate (..),
  Memory (..),
  Symbol (..),

  -- * Common instructions
  Op2 (..),
  Add (..),
  Call (..),
  Cmp (..),
  Je (..),
  Jmp (..),
  Lea (..),
  Mov (..),
  Pop (..),
  Push (..),
  Ret (..),
  Sub (..),
  Xor (..),
) where

import Data.Hashable (Hashable)
import Data.Int (Int64)
import Data.Kind (Type)
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Word (Word64)
import Metis.Literal (Literal (..))

class (Eq (Register isa), Show (Register isa), Hashable (Register isa)) => Isa isa where
  data Register isa :: Type
  data Instruction isa :: Type

  registerName :: Register isa -> Text

  generalPurposeRegisters :: Seq (Register isa)

data Immediate
  = Number Word64
  | Label Symbol
  deriving (Eq, Show)

class ToImmediate a where
  imm :: a -> Immediate

instance ToImmediate Literal where
  imm lit =
    case lit of
      Uint64 i -> Number (fromIntegral i)
      Bool b -> if b then Number 1 else Number 0

instance ToImmediate Word64 where
  imm = Number

instance ToImmediate Symbol where
  imm = Label

data Memory isa = Mem {base :: Register isa, offset :: Int64}

deriving instance (Eq (Register isa)) => Eq (Memory isa)
deriving instance (Show (Register isa)) => Show (Memory isa)

newtype Symbol = Symbol {value :: Text}
  deriving (Eq, Show)

class Call isa a where call :: a -> Instruction isa
class Pop isa a where pop :: a -> Instruction isa
class Push isa a where push :: a -> Instruction isa
class Jmp isa a where jmp :: a -> Instruction isa
class Je isa a where je :: a -> Instruction isa
class Ret isa a where ret :: a -> Instruction isa

data Op2 src dest = Op2 {src :: src, dest :: dest}
  deriving (Eq, Show)

class Add isa src dest where add :: Op2 src dest -> Instruction isa
class Lea isa src dest where lea :: Op2 src dest -> Instruction isa
class Mov isa src dest where mov :: Op2 src dest -> Instruction isa
class Sub isa src dest where sub :: Op2 src dest -> Instruction isa
class Xor isa src dest where xor :: Op2 src dest -> Instruction isa
class Cmp isa a b where cmp :: a -> b -> Instruction isa