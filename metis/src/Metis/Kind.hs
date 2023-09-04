{-# LANGUAGE DeriveGeneric #-}

module Metis.Kind (Kind (..)) where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data Kind = Type
  deriving (Eq, Show, Generic)

instance Hashable Kind