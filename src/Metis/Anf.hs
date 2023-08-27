{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Metis.Anf (
  Expr (..),
  Var (..),
  VarInfo (..),
  Simple (..),
  Compound (..),
  Binop (..),
  ExprInfo (..),

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
import Control.Monad.State.Class (get, gets, modify, put)
import Control.Monad.State.Strict (StateT, lift, runStateT)
import Data.Functor.Identity (runIdentity)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import Data.Word (Word64)
import qualified Metis.Core as Core
import Metis.Literal (Literal)
import Metis.Type (Type)
import qualified Metis.Type as Type

data Expr
  = Return Simple
  | LetS Var VarInfo Simple Expr
  | LetC Var VarInfo Compound Expr
  | IfThenElse Simple Expr Expr Expr
  | Jump Var Simple
  | Label Var Var Expr
  deriving (Show, Eq)

data Simple
  = Var Var
  | Name Text
  | Literal Literal
  deriving (Show, Eq)

data Compound
  = Binop Binop Simple Simple
  | Call Simple [Simple]
  deriving (Show, Eq)

data Binop = Add | Subtract
  deriving (Show, Eq)

newtype ExprInfo = ExprInfo {labelArgs :: Var -> Var}

data AnfBuilderState = AnfBuilderState
  { nextVar :: Word64
  , program :: Expr -> Expr
  , labelArgs :: HashMap Var Var
  }

newtype AnfBuilderT m a = AnfBuilderT {value :: StateT AnfBuilderState m a}
  deriving (Functor, Applicative, Monad)

runAnfBuilderT :: (Monad m) => AnfBuilderT m a -> m (AnfBuilderState, a)
runAnfBuilderT ma = do
  (a, s) <-
    runStateT
      ma.value
      AnfBuilderState
        { nextVar = 0
        , program = id
        , labelArgs =
            mempty
        }
  pure (s, a)

newtype Var = MkVar {value :: Word64}
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

block :: (Monad m) => Var -> Var -> AnfBuilderT m ()
block label arg = do
  emit $ Label label arg
  AnfBuilderT $ modify (\s -> (s :: AnfBuilderState){labelArgs = HashMap.insert label arg s.labelArgs})

programOf :: (Monad m) => AnfBuilderT m a -> AnfBuilderT m (Expr -> Expr, a)
programOf ma =
  AnfBuilderT $ do
    s <- get
    (a, s') <- lift $ runStateT ma.value s{program = id}
    put s'{program = s.program}
    pure (s'.program, a)

fromCore :: (a -> Var) -> Core.Expr a -> (ExprInfo, Expr)
fromCore toVar expr =
  ( ExprInfo
      { labelArgs = \label -> Maybe.fromMaybe (error $ show label <> " missing from label args map") $ HashMap.lookup label s.labelArgs
      }
  , s.program (Return simple)
  )
  where
    (s, simple) = runIdentity . runAnfBuilderT $ fromCoreExpr toVar expr

fromCoreExpr :: (Monad m) => (a -> Var) -> Core.Expr a -> AnfBuilderT m Simple
fromCoreExpr toVar expr =
  case expr of
    Core.Var var ->
      pure $ Var (toVar var)
    Core.Name name ->
      pure $ Name name
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
      var <-
        case value' of
          Var var ->
            pure var
          Name{} ->
            letS valueTy value'
          Literal{} ->
            letS valueTy value'
      fromCoreExpr (unvar (\() -> var) toVar) (fromScope rest)
    Core.IfThenElse _ cond then_ else_ -> do
      cond' <- fromCoreExpr toVar cond
      (then_', thenSimple) <- programOf $ fromCoreExpr toVar then_
      (else_', elseSimple) <- programOf $ fromCoreExpr toVar else_
      label <- freshVar
      emit $ IfThenElse cond' (then_' $ Jump label thenSimple) (else_' $ Jump label elseSimple)

      arg <- freshVar
      block label arg
      pure $ Var arg
    Core.Call ty function args -> do
      function' <- fromCoreExpr toVar function
      args' <- traverse (fromCoreExpr toVar) args
      Var <$> letC ty (Call function' args')