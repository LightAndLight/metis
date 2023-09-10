{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Metis.SSA.Var (
  Var,
  unsafeVar,
  MonadVar (..),
  VarT,
  runVarT,
) where

import Control.Monad.State.Strict (StateT, evalStateT, get, put)
import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.Hashable (Hashable (..))
import Data.Word (Word64)

newtype Var = Var {value :: Word64}
  deriving (Eq, Hashable, Show)

unsafeVar :: Word64 -> Var
unsafeVar = Var

class (Monad m) => MonadVar m where
  freshVar :: m Var
  default freshVar :: (m ~ t n, MonadTrans t, MonadVar n) => m Var
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