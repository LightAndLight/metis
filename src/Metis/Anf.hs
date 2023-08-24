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
  deriving (Show, Eq)

typeVarInfo :: Type -> VarInfo
typeVarInfo ty = VarInfo{size = Type.sizeOf ty}

fromCore :: (a -> (Var, Type)) -> Core.Expr a -> Expr
fromCore toVar expr =
  runIdentity . runAnfBuilderT $ do
    expr' <- fromCoreExpr toVar expr
    resultToExpr (Core.typeOf (snd . toVar) expr) expr'

splitExpr :: Expr -> (Expr -> Expr, Simple)
splitExpr expr =
  case expr of
    Simple simple -> (id, simple)
    LetS var info simple rest ->
      let (f, x) = splitExpr rest
       in (LetS var info simple . f, x)
    LetC var info compound rest ->
      let (f, x) = splitExpr rest
       in (LetC var info compound . f, x)

data FromCoreResult
  = SimpleResult Simple
  | CompoundResult Compound
  | ExprResult Expr

resultToExpr ::
  (Monad m) =>
  Type ->
  FromCoreResult ->
  AnfBuilderT m Expr
resultToExpr ty result =
  case result of
    SimpleResult simple -> letS (typeVarInfo ty) simple (pure . Simple . Var)
    CompoundResult compound -> letC (typeVarInfo ty) compound (pure . Simple . Var)
    ExprResult expr -> pure expr

letResult :: (Monad m) => FromCoreResult -> Type -> (Var -> AnfBuilderT m Expr) -> AnfBuilderT m Expr
letResult value ty rest =
  case value of
    SimpleResult valueSimple ->
      letS (typeVarInfo ty) valueSimple rest
    CompoundResult valueCompound ->
      letC (typeVarInfo ty) valueCompound rest
    ExprResult valueExpr -> do
      let (valueExprInit, valueExprLast) = splitExpr valueExpr
      valueExprInit <$> letS (typeVarInfo ty) valueExprLast rest

fromCoreExpr :: (Monad m) => (a -> (Var, Type)) -> Core.Expr a -> AnfBuilderT m FromCoreResult
fromCoreExpr toVar expr =
  case expr of
    Core.Var var -> pure . SimpleResult $ Var (fst $ toVar var)
    Core.Literal lit -> pure . SimpleResult $ Literal lit
    Core.Add ty a b -> do
      a' <- fromCoreExpr toVar a
      ExprResult
        <$> letResult
          a'
          (Core.typeOf (snd . toVar) a)
          ( \aVar -> do
              b' <- fromCoreExpr toVar b
              letResult
                b'
                (Core.typeOf (snd . toVar) b)
                ( \bVar -> do
                    letC (typeVarInfo ty) (Binop Add (Var aVar) (Var bVar)) (pure . Simple . Var)
                )
          )
    Core.Subtract ty a b -> do
      a' <- fromCoreExpr toVar a
      ExprResult
        <$> letResult
          a'
          (Core.typeOf (snd . toVar) a)
          ( \aVar -> do
              b' <- fromCoreExpr toVar b
              letResult
                b'
                (Core.typeOf (snd . toVar) b)
                ( \bVar -> do
                    letC (typeVarInfo ty) (Binop Subtract (Var aVar) (Var bVar)) (pure . Simple . Var)
                )
          )
    Core.Let ty _ valueTy value rest -> do
      value' <- fromCoreExpr toVar value
      case value' of
        SimpleResult valueSimple ->
          ExprResult
            <$> letS
              (typeVarInfo valueTy)
              valueSimple
              (\var -> fromCoreExpr (unvar (\() -> (var, valueTy)) toVar) (fromScope rest) >>= resultToExpr ty)
        CompoundResult valueCompound ->
          ExprResult
            <$> letC
              (typeVarInfo valueTy)
              valueCompound
              (\var -> fromCoreExpr (unvar (\() -> (var, valueTy)) toVar) (fromScope rest) >>= resultToExpr ty)
        ExprResult valueExpr -> do
          let (valueExprInit, valueExprLast) = splitExpr valueExpr
          ExprResult . valueExprInit
            <$> letS
              (typeVarInfo valueTy)
              valueExprLast
              (\var -> fromCoreExpr (unvar (\() -> (var, valueTy)) toVar) (fromScope rest) >>= resultToExpr ty)