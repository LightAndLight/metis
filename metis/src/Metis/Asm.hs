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
  quad,
  string,
  Expr (..),
  ToExpr (..),
  printAsm,
) where

import Data.Text (Text)
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Word (Word64)
import Metis.Isa (Instruction, Symbol (..))

data Asm isa = Asm
  { data_ :: [DataEntry]
  , text :: [Block isa]
  }

data DataEntry = DataEntry {label :: Text, content :: [Directive]}

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
  = Quad Expr
  | String Expr
  deriving (Eq, Show)

data Expr
  = Word64 Word64
  | Symbol Symbol
  | ExprString Text
  deriving (Eq, Show)

class ToExpr a where
  toExpr :: a -> Expr

instance ToExpr Word64 where
  toExpr = Word64

instance ToExpr Symbol where
  toExpr = Metis.Asm.Symbol

instance ToExpr Text where
  toExpr = ExprString

quad :: (ToExpr a) => a -> Directive
quad = Quad . toExpr

string :: (ToExpr a) => a -> Directive
string = String . toExpr

printAsm :: (Instruction isa -> Builder) -> Asm isa -> Builder
printAsm printInstruction asm =
  foldMap (<> "\n") $
    ( if null asm.data_
        then []
        else
          [".data"]
            <> fmap
              ( \DataEntry{label, content} ->
                  Builder.fromText label
                    <> ":\n"
                    <> foldMap ((<> "\n") . printDirective) content
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
      Quad e -> "quad " <> printExpr e
      String e -> "string " <> printExpr e

printExpr :: Expr -> Builder
printExpr e =
  case e of
    Word64 w ->
      Builder.fromString (show w)
    Metis.Asm.Symbol s ->
      Builder.fromText s.value
    ExprString s ->
      Builder.fromString (show s)