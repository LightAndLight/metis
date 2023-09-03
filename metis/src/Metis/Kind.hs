module Metis.Kind (Kind (..)) where

data Kind = Type | Arrow Kind Kind
  deriving (Eq, Show)