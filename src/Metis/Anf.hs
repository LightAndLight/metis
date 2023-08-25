{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Metis.Anf (
  Expr (..),
  Var (..),
  VarInfo (..),
  Simple (..),
  Compound (..),
  Binop (..),

  -- * Core translation
  fromCore,
  fromCoreExpr,

  -- * ANF expression builder
  AnfBuilderT,
  runAnfBuilderT,
  freshVar,
  emit,
  letS,
  letC,
) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad.State.Class (gets, modify)
import Control.Monad.State.Strict (StateT, runStateT)
import Data.Functor.Identity (runIdentity)
import Data.Hashable (Hashable)
import Data.Word (Word64)
import qualified Metis.Core as Core
import Metis.Literal (Literal)
import Metis.Type (Type)
import qualified Metis.Type as Type

data Expr
  = Simple Simple
  | LetS Var VarInfo Simple Expr
  | LetC Var VarInfo Compound Expr
  deriving (Show, Eq)

data Simple
  = Var Var
  | Literal Literal
  deriving (Show, Eq)

data Compound
  = Binop Binop Simple Simple
  deriving (Show, Eq)

data Binop = Add | Subtract
  deriving (Show, Eq)

data AnfBuilderState = AnfBuilderState {nextVar :: Word64, program :: Expr -> Expr}

newtype AnfBuilderT m a = AnfBuilderT {value :: StateT AnfBuilderState m a}
  deriving (Functor, Applicative, Monad)

runAnfBuilderT :: (Monad m) => AnfBuilderT m Simple -> m Expr
runAnfBuilderT ma = do
  (a, s) <- runStateT ma.value AnfBuilderState{nextVar = 0, program = id}
  pure $ s.program (Simple a)

newtype Var = MkVar Word64
  deriving (Show, Eq, Hashable)

freshVar :: (Monad m) => AnfBuilderT m Var
freshVar =
  AnfBuilderT $ do
    n <- gets (.nextVar)
    modify (\s -> s{nextVar = n + 1})
    pure $ MkVar n

emit :: (Monad m) => (Expr -> Expr) -> AnfBuilderT m ()
emit f = AnfBuilderT $ modify (\s -> s{program = s.program . f})

data VarInfo = VarInfo {size :: Word64}
  deriving (Show, Eq)

typeVarInfo :: Type -> VarInfo
typeVarInfo ty = VarInfo{size = Type.sizeOf ty}

letS :: (Monad m) => Type -> Simple -> AnfBuilderT m Var
letS ty value = do
  var <- freshVar
  emit $ LetS var (typeVarInfo ty) value
  pure var

letC :: (Monad m) => Type -> Compound -> AnfBuilderT m Var
letC ty value = do
  var <- freshVar
  emit $ LetC var (typeVarInfo ty) value
  pure var

fromCore :: (a -> Var) -> Core.Expr a -> Expr
fromCore toVar =
  runIdentity . runAnfBuilderT . fromCoreExpr toVar

fromCoreExpr :: (Monad m) => (a -> Var) -> Core.Expr a -> AnfBuilderT m Simple
fromCoreExpr toVar expr =
  case expr of
    Core.Var var ->
      pure $ Var (toVar var)
    Core.Literal lit ->
      pure $ Literal lit
    Core.Add ty a b -> do
      a' <- fromCoreExpr toVar a
      b' <- fromCoreExpr toVar b
      Var <$> letC ty (Binop Add a' b')
    Core.Subtract ty a b -> do
      a' <- fromCoreExpr toVar a
      b' <- fromCoreExpr toVar b
      Var <$> letC ty (Binop Subtract a' b')
    Core.Let _ _ valueTy value rest -> do
      value' <- fromCoreExpr toVar value
      var <- letS valueTy value'
      fromCoreExpr (unvar (\() -> var) toVar) (fromScope rest)