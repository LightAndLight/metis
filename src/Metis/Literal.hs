module Metis.Literal (Literal (..)) where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Word (Word16, Word32, Word64, Word8)

data Literal
  = Int8 Int8
  | Int16 Int16
  | Int32 Int32
  | Int64 Int64
  | Uint8 Word8
  | Uint16 Word16
  | Uint32 Word32
  | Uint64 Word64
