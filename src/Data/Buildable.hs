{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

module Data.Buildable (
  Buildable (..),
  fromListR,
  fromListL,
  fromListL',
  IndexedBuildable (..),
  ifromListR,
  ifromListL,
  ifromListL',
) where

import Data.Foldable (foldl')
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

{- | Laws:

@foldr cons nil (buildr f) = f cons nil@
@foldl snoc nil (buildl f) = f snoc nil@
-}
class Buildable f where
  buildr :: (forall r. (a -> r -> r) -> r -> r) -> f a
  buildl :: (forall r. (r -> a -> r) -> r -> r) -> f a

instance Buildable [] where
  buildr f = f (:) []
  buildl f = f (\as a -> as . (:) a) id []

instance Buildable Seq where
  buildr f = f (Seq.<|) Seq.empty
  buildl f = f (Seq.|>) Seq.empty

fromListR :: (Buildable f) => [a] -> f a
fromListR as = buildr (\cons nil -> foldr cons nil as)

fromListL :: (Buildable f) => [a] -> f a
fromListL as = buildl (\snoc nil -> foldl snoc nil as)

fromListL' :: (Buildable f) => [a] -> f a
fromListL' as = buildl (\snoc nil -> foldl' snoc nil as)

class IndexedBuildable i f | f -> i where
  ibuildr :: (forall r. (i -> a -> r -> r) -> r -> r) -> f a
  ibuildl :: (forall r. (r -> i -> a -> r) -> r -> r) -> f a

instance (Hashable k) => IndexedBuildable k (HashMap k) where
  ibuildr f = f HashMap.insert mempty
  ibuildl f = f (\rest k v -> HashMap.insert k v rest) mempty

ifromListR :: (IndexedBuildable i f) => [(i, a)] -> f a
ifromListR as = ibuildr (\cons nil -> foldr (uncurry cons) nil as)

ifromListL :: (IndexedBuildable i f) => [(i, a)] -> f a
ifromListL as = ibuildl (\snoc nil -> foldl (uncurry . snoc) nil as)

ifromListL' :: (IndexedBuildable i f) => [(i, a)] -> f a
ifromListL' as = ibuildl (\snoc nil -> foldl' (uncurry . snoc) nil as)