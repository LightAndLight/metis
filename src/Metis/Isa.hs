{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

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
  Lea (..),
  Mov (..),
  Pop (..),
  Push (..),
  Sub (..),
  Xor (..),
) where

import Data.Int (Int64)
import Data.Kind (Type)
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Word (Word64)
import Metis.Literal (Literal (..))

class (Eq (Register isa), Show (Register isa)) => Isa isa where
  data Register isa :: Type
  data Instruction isa :: Type

  registerName :: Register isa -> Text

  generalPurposeRegisters :: Seq (Register isa)

newtype Immediate = Imm Word64

class ToImmediate a where
  imm :: a -> Immediate

instance ToImmediate Literal where
  imm lit =
    case lit of
      Uint64 i -> Imm (fromIntegral i)

instance ToImmediate Word64 where
  imm = Imm

data Memory isa = Mem {base :: Register isa, offset :: Int64}

newtype Symbol = Symbol {value :: Text}

class Call isa a where call :: a -> Instruction isa
class Pop isa a where pop :: a -> Instruction isa
class Push isa a where push :: a -> Instruction isa

data Op2 src dest = Op2 {src :: src, dest :: dest}

class Add isa src dest where add :: Op2 src dest -> Instruction isa
class Lea isa src dest where lea :: Op2 src dest -> Instruction isa
class Mov isa src dest where mov :: Op2 src dest -> Instruction isa
class Sub isa src dest where sub :: Op2 src dest -> Instruction isa
class Xor isa src dest where xor :: Op2 src dest -> Instruction isa