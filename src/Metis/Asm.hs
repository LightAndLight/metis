{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Metis.Asm (
  Asm (..),
  DataEntry (..),
  Block (..),
  BlockAttribute (..),
  printAsm,
) where

import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Metis.Isa (Instruction)

data Asm isa = Asm
  { data_ :: [DataEntry]
  , text :: [Block isa]
  }

data DataEntry = DataString {label :: Text, content :: Text}

data Block isa = Block
  { label :: Text
  , attributes :: [BlockAttribute]
  , instructions :: [Instruction isa]
  }

data BlockAttribute = Global
  deriving (Eq)

printAsm :: (Instruction isa -> Builder) -> Asm isa -> Builder
printAsm printInstruction asm =
  foldMap (<> "\n") $
    ( if null asm.data_
        then []
        else
          [".data"]
            <> fmap
              ( \DataString{label, content} ->
                  Builder.fromText label
                    <> ": "
                    <> ".string "
                    <> Builder.fromString (show content)
              )
              asm.data_
    )
      <> [".text"]
      <> ( asm.text >>= \Block{label, attributes, instructions} ->
            [".global " <> Builder.fromText label | Global `elem` attributes]
              <> [Builder.fromText label <> ":"]
              <> fmap printInstruction instructions
         )
