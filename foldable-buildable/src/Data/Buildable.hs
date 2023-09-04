{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Buildable (
  Buildable (..),
  collectR,
  collectL,
  collectL',
) where

import Control.Monad.ST (ST, runST)
import Data.Foldable (foldl')
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import Data.Kind (Type)
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

Given @Foldable f@ and @Buildable (f a), Item (f a) ~ a@

@foldr \@f cons nil (buildr f) = f cons nil@
@foldl \@f snoc nil (buildl f) = f snoc nil@
@foldMap \@f into (buildMap f) = f into@
-}
class Buildable b where
  type Item b :: Type

  buildr :: (forall r. (Item b -> r -> r) -> r -> r) -> b
  buildr f = buildMap (\into -> f (\a rest -> (into a <>) . rest) id mempty)

  buildl :: (forall r. (r -> Item b -> r) -> r -> r) -> b
  buildl f = buildMap (\into -> f (\acc a -> acc . (into a <>)) id mempty)

  buildMap :: (forall m. (Monoid m) => (Item b -> m) -> m) -> b
  buildMap f = buildr (\cons nil -> appEndo (f (Endo . cons)) nil)

instance Buildable [a] where
  type Item [a] = a

  buildr f = f (:) []
  buildl f = f (\as a -> as . (:) a) id []
  buildMap f = f pure

instance Buildable (Seq a) where
  type Item (Seq a) = a

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

instance Buildable (Vector a) where
  type Item (Vector a) = a

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

instance (Hashable a) => Buildable (HashSet a) where
  type Item (HashSet a) = a

  buildr f = f HashSet.insert HashSet.empty
  buildl f = f (flip HashSet.insert) HashSet.empty
  buildMap f = f HashSet.singleton

instance (Hashable k) => Buildable (HashMap k v) where
  type Item (HashMap k v) = (k, v)

  buildr f = f (uncurry HashMap.insert) HashMap.empty
  buildl f = f (\acc (k, v) -> HashMap.insert k v acc) HashMap.empty
  buildMap f = f (uncurry HashMap.singleton)

collectR :: forall b f a. (Foldable f, Buildable b, Item b ~ a) => f a -> b
collectR as = buildr (\cons nil -> foldr cons nil as)

collectL :: forall b f a. (Foldable f, Buildable b, Item b ~ a) => f a -> b
collectL as = buildl (\snoc nil -> foldl snoc nil as)

collectL' :: forall b f a. (Foldable f, Buildable b, Item b ~ a) => f a -> b
collectL' as = buildl (\snoc nil -> foldl' snoc nil as)