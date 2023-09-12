{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Metis.Asm.BuilderNew (AsmBuilderT, runAsmBuilderT) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State.Strict (StateT, execStateT, gets, modify)
import qualified Data.Text as Text
import Data.Word (Word64)
import Metis.Asm.ClassNew (MonadAsm (..))
import Metis.AsmNew (Asm (..), Block (..), DataEntry (..), string)
import Metis.IsaNew (Isa, Symbol (..))

data AsmBuilderState isa = AsmBuilderState
  { nextString :: Word64
  , asm :: Asm isa
  }

initialAsmBuilderState :: AsmBuilderState isa
initialAsmBuilderState = AsmBuilderState{nextString = 0, asm = Asm{data_ = [], text = []}}

newtype AsmBuilderT isa m a = AsmBuilderT {value :: StateT (AsmBuilderState isa) m a}
  deriving (Functor, Applicative, Monad, MonadFix, MonadIO)

runAsmBuilderT :: (Monad m) => AsmBuilderT isa m () -> m (Asm isa)
runAsmBuilderT ma = do
  s <- execStateT ma.value initialAsmBuilderState
  pure s.asm

instance (Isa isa, Monad m) => MonadAsm isa (AsmBuilderT isa m) where
  string content =
    AsmBuilderT $ do
      label <- do
        n <- gets (.nextString)
        modify (\s -> s{nextString = n + 1})
        pure . Text.pack $ "string_" <> show n
      modify (\s -> s{asm = s.asm{data_ = s.asm.data_ <> [DataEntry{label, content = [Metis.AsmNew.string content]}]}})
      pure $ Symbol label

  struct label content = do
    AsmBuilderT $ do
      modify (\s -> s{asm = s.asm{data_ = s.asm.data_ <> [DataEntry{label, content}]}})
      pure $ Symbol label

  block label attributes registerHints statements =
    AsmBuilderT $ do
      modify (\s -> s{asm = s.asm{text = s.asm.text <> [Block{label, attributes, registerHints, statements}]}})
      pure $ Symbol label