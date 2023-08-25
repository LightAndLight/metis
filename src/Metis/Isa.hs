{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.Isa (
  Isa (..),
  Immediate (..),
  ToImmediate (..),
  Memory (..),

  -- * Common instructions
  Mov (..),
  Add (..),
  Sub (..),
  Push (..),
  Pop (..),
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

data Memory isa = Mem {base :: Register isa, offset :: Int64}

class Mov isa a b where mov :: a -> b -> Instruction isa
class Add isa a b where add :: a -> b -> Instruction isa
class Sub isa a b where sub :: a -> b -> Instruction isa
class Push isa a where push :: a -> Instruction isa
class Pop isa a where pop :: a -> Instruction isa