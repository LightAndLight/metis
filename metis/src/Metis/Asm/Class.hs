{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}

module Metis.Asm.Class (MonadAsm (..)) where

import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.Text (Text)
import Metis.Asm (BlockAttribute, Statement)
import Metis.Isa (Symbol)

class (Monad m) => MonadAsm isa m | m -> isa where
  string :: Text -> m Symbol
  default string :: (m ~ t n, MonadTrans t, MonadAsm isa n) => Text -> m Symbol
  string value = lift $ string value

  block :: Text -> [BlockAttribute] -> [Statement isa] -> m Symbol
  default block :: (m ~ t n, MonadTrans t, MonadAsm isa n) => Text -> [BlockAttribute] -> [Statement isa] -> m Symbol
  block label attributes statements = lift $ block label attributes statements