{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

import Control.Monad.ST (ST, runST)
import Data.Foldable (foldl')
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Monoid (Endo (..))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MVector
import GHC.Exts (Int#, (+#))
import GHC.Int (Int (..))

{- | Laws:

@foldr cons nil (buildr f) = f cons nil@
@foldl snoc nil (buildl f) = f snoc nil@
@foldMap into (buildMap f) = f into@
-}
class Buildable f where
  buildr :: (forall r. (a -> r -> r) -> r -> r) -> f a
  buildr f = buildMap (\into -> f (\a rest -> (into a <>) . rest) id mempty)

  buildl :: (forall r. (r -> a -> r) -> r -> r) -> f a
  buildl f = buildMap (\into -> f (\acc a -> acc . (into a <>)) id mempty)

  buildMap :: (forall m. (Monoid m) => (a -> m) -> m) -> f a
  buildMap f = buildr (\cons nil -> appEndo (f (Endo . cons)) nil)

instance Buildable [] where
  buildr f = f (:) []
  buildl f = f (\as a -> as . (:) a) id []
  buildMap f = f pure

instance Buildable Seq where
  buildr f = f (Seq.<|) Seq.empty
  buildl f = f (Seq.|>) Seq.empty
  buildMap f = f Seq.singleton

data VectorBuilder a = VectorBuilder Int# (forall s. MVector s a -> Int# -> ST s ())

instance Semigroup (VectorBuilder a) where
  {-# INLINEABLE (<>) #-}
  VectorBuilder a f <> VectorBuilder b g =
    VectorBuilder
      (a +# b)
      (\v index -> f v index *> g v (index +# a))

instance Monoid (VectorBuilder a) where
  {-# INLINE mempty #-}
  mempty = VectorBuilder 0# (\_ _ -> pure ())

instance Buildable Vector where
  buildMap f = toVector (f into)
   where
    {-# INLINE into #-}
    into :: a -> VectorBuilder a
    into a = VectorBuilder 1# (\v index -> MVector.unsafeWrite v (I# index) a)

    {-# INLINE toVector #-}
    toVector :: VectorBuilder a -> Vector a
    toVector (VectorBuilder size make) =
      runST $ do
        v <- MVector.unsafeNew (I# size)
        make v 0#
        Vector.unsafeFreeze v

fromListR :: (Buildable f) => [a] -> f a
fromListR as = buildr (\cons nil -> foldr cons nil as)

fromListL :: (Buildable f) => [a] -> f a
fromListL as = buildl (\snoc nil -> foldl snoc nil as)

fromListL' :: (Buildable f) => [a] -> f a
fromListL' as = buildl (\snoc nil -> foldl' snoc nil as)

{- | Laws:

@ifoldr cons nil (ibuildr f) = f cons nil@
@ifoldl snoc nil (ibuildl f) = f snoc nil@
@ifoldMap into (ibuildMap f) = f into@
-}
class IndexedBuildable i f | f -> i where
  ibuildr :: (forall r. (i -> a -> r -> r) -> r -> r) -> f a
  ibuildr f = ibuildMap (\into -> f (\i a rest -> (into i a <>) . rest) id mempty)

  ibuildl :: (forall r. (r -> i -> a -> r) -> r -> r) -> f a
  ibuildl f = ibuildMap (\into -> f (\acc i a -> acc . (into i a <>)) id mempty)

  ibuildMap :: (forall m. (Monoid m) => (i -> a -> m) -> m) -> f a
  ibuildMap f = ibuildr (\cons nil -> appEndo (f (\i -> Endo . cons i)) nil)

instance (Hashable k) => IndexedBuildable k (HashMap k) where
  ibuildr f = f HashMap.insert mempty
  ibuildl f = f (\rest k v -> HashMap.insert k v rest) mempty

ifromListR :: (IndexedBuildable i f) => [(i, a)] -> f a
ifromListR as = ibuildr (\cons nil -> foldr (uncurry cons) nil as)

ifromListL :: (IndexedBuildable i f) => [(i, a)] -> f a
ifromListL as = ibuildl (\snoc nil -> foldl (uncurry . snoc) nil as)

ifromListL' :: (IndexedBuildable i f) => [(i, a)] -> f a
ifromListL' as = ibuildl (\snoc nil -> foldl' (uncurry . snoc) nil as)