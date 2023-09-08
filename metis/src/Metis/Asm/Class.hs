{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}

module Metis.Asm.Class (MonadAsm (..)) where

import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.HashSet (HashSet)
import Data.Text (Text)
import Metis.Asm (BlockAttribute, Directive, Statement)
import Metis.Isa (Register, Symbol)

class (Monad m) => MonadAsm isa m | m -> isa where
  string :: Text -> m Symbol
  default string :: (m ~ t n, MonadTrans t, MonadAsm isa n) => Text -> m Symbol
  string value = lift $ string value

  struct :: Text -> [Directive] -> m Symbol
  default struct :: (m ~ t n, MonadTrans t, MonadAsm isa n) => Text -> [Directive] -> m Symbol
  struct label values = lift $ struct label values

  block :: Text -> [BlockAttribute] -> Maybe (HashSet (Register isa)) -> [Statement isa] -> m Symbol
  default block :: (m ~ t n, MonadTrans t, MonadAsm isa n) => Text -> [BlockAttribute] -> Maybe (HashSet (Register isa)) -> [Statement isa] -> m Symbol
  block label attributes registerHints statements = lift $ block label attributes registerHints statements