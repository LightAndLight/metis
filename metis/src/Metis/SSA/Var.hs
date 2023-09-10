{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Metis.SSA.Var (
  Var,
  eqVar,
  unsafeVar,
  AnyVar (..),
  MonadVar (..),
  VarT,
  runVarT,
) where

import Control.Monad.State.Strict (StateT, evalStateT, get, put)
import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.Hashable (Hashable (..))
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.Word (Word64)
import Unsafe.Coerce (unsafeCoerce)

newtype Var a = Var {value :: Word64}
  deriving (Eq, Hashable, Show)

unsafeVar :: Word64 -> Var a
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

deriving instance Show AnyVar

instance Hashable AnyVar where
  hashWithSalt salt (AnyVar a) = hashWithSalt salt a.value

class (Monad m) => MonadVar m where
  freshVar :: m (Var a)
  default freshVar :: (m ~ t n, MonadTrans t, MonadVar n) => m (Var a)
  freshVar = lift freshVar

newtype VarT m a = VarT (StateT Word64 m a)
  deriving (Functor, Applicative, Monad, MonadTrans)

runVarT :: (Monad m) => VarT m a -> m a
runVarT (VarT ma) = evalStateT ma 0

instance (Monad m) => MonadVar (VarT m) where
  freshVar =
    VarT $ do
      n <- get
      put $ n + 1
      pure $ Var n