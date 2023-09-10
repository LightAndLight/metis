{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Metis.SSA.Var (Var, eqVar, unsafeVar, AnyVar (..)) where

import Data.Hashable (Hashable (..))
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Unsafe.Coerce (unsafeCoerce)

newtype Var a = Var {value :: Int}
  deriving (Eq, Hashable, Show)

unsafeVar :: Int -> Var a
unsafeVar = Var

eqVar :: forall a b. Var a -> Var b -> Maybe (a :~: b)
eqVar (Var a) (Var b) =
  if a == b
    then Just (unsafeCoerce @(a :~: a) @(a :~: b) Refl)
    else Nothing

data AnyVar :: Type where
  AnyVar :: Var a -> AnyVar

instance Eq AnyVar where
  AnyVar a == AnyVar b = a.value == b.value

instance Hashable AnyVar where
  hashWithSalt salt (AnyVar a) = hashWithSalt salt a.value