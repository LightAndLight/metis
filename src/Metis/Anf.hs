{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Metis.Anf (
  Expr (..),
  Var,
  VarInfo (..),
  Simple (..),
  Compound (..),
  Binop (..),

  -- * Core translation
  fromCore,
  fromCoreExpr,
  fromCoreCompound,
  fromCoreSimple,

  -- * ANF expression builder
  AnfBuilderT,
  runAnfBuilderT,
  freshVar,
  letS,
  letC,
) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad.State.Class (get, put)
import Control.Monad.State.Strict (StateT, evalStateT)
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

data Simple
  = Var Var
  | Literal Literal

data Compound
  = Binop Binop Simple Simple

data Binop = Add | Subtract

newtype AnfBuilderT m a = AnfBuilderT {value :: StateT Word64 m a}
  deriving (Functor, Applicative, Monad)

runAnfBuilderT :: (Monad m) => AnfBuilderT m a -> m a
runAnfBuilderT ma = evalStateT ma.value 0

newtype Var = MkVar Word64
  deriving (Show, Eq, Hashable)

freshVar :: (Monad m) => AnfBuilderT m Var
freshVar =
  AnfBuilderT $ do
    n <- get
    put $ n + 1
    pure $ MkVar n

letS :: (Monad m) => VarInfo -> Simple -> (Var -> AnfBuilderT m Expr) -> AnfBuilderT m Expr
letS varInfo value mkRest = do
  var <- freshVar
  LetS var varInfo value <$> mkRest var

letC :: (Monad m) => VarInfo -> Compound -> (Var -> AnfBuilderT m Expr) -> AnfBuilderT m Expr
letC varInfo value mkRest = do
  var <- freshVar
  LetC var varInfo value <$> mkRest var

data VarInfo = VarInfo {size :: Word64}

typeVarInfo :: Type -> VarInfo
typeVarInfo ty = VarInfo{size = Type.sizeOf ty}

fromCore :: (a -> Var) -> Core.Expr a -> Expr
fromCore toVar = runIdentity . runAnfBuilderT . fromCoreExpr toVar

fromCoreExpr :: (Monad m) => (a -> Var) -> Core.Expr a -> AnfBuilderT m Expr
fromCoreExpr toVar expr =
  case expr of
    Core.Simple s ->
      pure $ Simple (fromCoreSimple toVar s)
    Core.LetS _ ty value rest ->
      letS
        (typeVarInfo ty)
        (fromCoreSimple toVar value)
        (\var -> fromCoreExpr (unvar (\() -> var) toVar) $ fromScope rest)
    Core.LetC _ ty value rest ->
      letC
        (typeVarInfo ty)
        (fromCoreCompound toVar value)
        (\var -> fromCoreExpr (unvar (\() -> var) toVar) $ fromScope rest)

fromCoreCompound :: (a -> Var) -> Core.Compound a -> Compound
fromCoreCompound toVar compound =
  case compound of
    Core.Add a b ->
      Binop Add (fromCoreSimple toVar a) (fromCoreSimple toVar b)
    Core.Subtract a b ->
      Binop Subtract (fromCoreSimple toVar a) (fromCoreSimple toVar b)

fromCoreSimple :: (a -> Var) -> Core.Simple a -> Simple
fromCoreSimple toVar simple =
  case simple of
    Core.Var var -> Var (toVar var)
    Core.Literal lit -> Literal lit