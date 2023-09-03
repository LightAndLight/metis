{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Metis.Asm (
  Asm (..),
  DataEntry (..),
  Block (..),
  BlockAttribute (..),
  Statement (..),
  Directive (..),
  printAsm,
) where

import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Word (Word64)
import Metis.Isa (Instruction)

data Asm isa = Asm
  { data_ :: [DataEntry]
  , text :: [Block isa]
  }

data DataEntry = DataString {label :: Text, content :: Text}

data Block isa = Block
  { label :: Text
  , attributes :: [BlockAttribute]
  , statements :: [Statement isa]
  }

data BlockAttribute = Global
  deriving (Eq)

data Statement isa
  = Instruction (Instruction isa)
  | Directive Directive

deriving instance (Eq (Instruction isa)) => Eq (Statement isa)
deriving instance (Show (Instruction isa)) => Show (Statement isa)

data Directive
  = Quad Word64
  deriving (Eq, Show)

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
      <> ( asm.text >>= \Block{label, attributes, statements} ->
            [".global " <> Builder.fromText label | Global `elem` attributes]
              <> [Builder.fromText label <> ":"]
              <> fmap (printStatement printInstruction) statements
         )

printStatement :: (Instruction isa -> Builder) -> Statement isa -> Builder
printStatement printInstruction statement =
  case statement of
    Instruction instruction ->
      printInstruction instruction
    Directive directive ->
      printDirective directive

printDirective :: Directive -> Builder
printDirective directive =
  "."
    <> case directive of
      Quad q -> "quad " <> Builder.fromString (show q)