{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Metis.Asm (
  Asm (..),
  DataEntry (..),
  Block (..),
  BlockAttribute (..),
  printAsm,

  -- * Builder
  AsmBuilderT,
  runAsmBuilderT,
  string,
  block,
) where

import Control.Monad.State.Strict (StateT, execStateT, gets, modify)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Word (Word64)
import Metis.Isa (Instruction, Symbol (..))

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
    [".data"]
      <> fmap
        ( \DataString{label, content} ->
            Builder.fromText label
              <> ": "
              <> ".string "
              <> Builder.fromString (show content)
        )
        asm.data_
      <> [".text"]
      <> ( asm.text >>= \Block{label, attributes, instructions} ->
            [".global " <> Builder.fromText label | Global `elem` attributes]
              <> [Builder.fromText label <> ":"]
              <> fmap printInstruction instructions
         )

data AsmBuilderState isa = AsmBuilderState
  { nextString :: Word64
  , asm :: Asm isa
  }

initialAsmBuilderState :: AsmBuilderState isa
initialAsmBuilderState = AsmBuilderState{nextString = 0, asm = Asm{data_ = [], text = []}}

newtype AsmBuilderT isa m a = AsmBuilderT {value :: StateT (AsmBuilderState isa) m a}
  deriving (Functor, Applicative, Monad)

runAsmBuilderT :: (Monad m) => AsmBuilderT isa m () -> m (Asm isa)
runAsmBuilderT ma = do
  s <- execStateT ma.value initialAsmBuilderState
  pure s.asm

string :: (Monad m) => Text -> AsmBuilderT isa m Symbol
string content =
  AsmBuilderT $ do
    label <- do
      n <- gets (.nextString)
      modify (\s -> s{nextString = n + 1})
      pure . Text.pack $ "string_" <> show n
    modify (\s -> s{asm = s.asm{data_ = s.asm.data_ <> [DataString{label, content}]}})
    pure $ Symbol label

block :: (Monad m) => Text -> [BlockAttribute] -> [Instruction isa] -> AsmBuilderT isa m Symbol
block label attributes instructions =
  AsmBuilderT $ do
    modify (\s -> s{asm = s.asm{text = s.asm.text <> [Block{label, attributes, instructions}]}})
    pure $ Symbol label