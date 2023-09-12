{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Metis.SSA (
  Instruction (..),
  Simple (..),
  typeOf,
  Compound (..),
  TypeDictField (..),
  typeDictFieldOffset,
  Binop (..),
  Terminator (..),
  Label (..),
  Block (..),
  FromCoreEnv (..),
  FromCoreState (..),
  initialFromCoreState,
  fromCoreExpr,
  fromCoreType,

  -- * Internals
  CallTypeInfo (..),
  calledFunctionType,
) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Data.DList (DList)
import qualified Data.DList as DList
import qualified Data.Either as Either
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Int (Int64)
import Data.Text (Text)
import Data.Traversable (for)
import Data.Void (Void, absurd)
import Data.Word (Word64)
import qualified Metis.Core as Core
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.SSA.Var (MonadVar, Var)
import qualified Metis.SSA.Var
import Metis.Type (Type)
import qualified Metis.Type as Type

data Instruction
  = LetS Var (Type Var) Simple
  | LetC Var (Type Var) Compound
  deriving (Eq, Show)

data Simple
  = Var Var
  | Name Text
  | Literal Literal
  | Type (Type Var)
  deriving (Show, Eq)

typeOf ::
  (Var -> Kind) ->
  (Text -> Type ty) ->
  (Var -> Type ty) ->
  Simple ->
  Either Kind (Type ty)
typeOf varKinds nameTys varTys simple =
  case simple of
    Var var -> Right $ varTys var
    Name name -> Right $ nameTys name
    Literal lit -> Right $ Literal.typeOf lit
    Type ty -> Left $ Type.kindOf varKinds ty

data Compound
  = Binop Binop Simple Simple
  | Call Simple [Var]
  | Alloca (Type Var)
  | Store Simple Simple
  | Load Simple
  | GetTypeDictField Simple TypeDictField
  deriving (Show, Eq)

data TypeDictField
  = TypeDictSize
  | TypeDictMove
  deriving (Show, Eq)

typeDictFieldOffset :: TypeDictField -> Int64
typeDictFieldOffset field =
  case field of
    TypeDictSize -> 0
    TypeDictMove -> 8

data Binop = Add | Subtract
  deriving (Show, Eq)

data Terminator
  = Return Simple
  | IfThenElse Simple Label Label
  | Jump Label Simple
  deriving (Eq, Show)

newtype Label = Label Text
  deriving (Eq, Show)

data Block = Block
  { name :: Text
  , params :: [Var]
  , instructions :: [Instruction]
  , terminator :: Terminator
  }
  deriving (Eq, Show)

data FromCoreEnv = FromCoreEnv
  {nameTypes :: Text -> Type Void}

data FromCoreState = FromCoreState
  { previousBlocks :: DList Block
  , currentName :: Text
  , currentParams :: [Var]
  , currentInstructions :: DList Instruction
  , varTypes :: HashMap Var (Type Var)
  }

initialFromCoreState :: FromCoreState
initialFromCoreState =
  FromCoreState
    { previousBlocks = mempty
    , currentName = "unnamed"
    , currentParams = []
    , currentInstructions = mempty
    , varTypes = mempty
    }

emit :: (MonadState FromCoreState m) => Instruction -> m ()
emit inst = modify (\s -> s{currentInstructions = DList.snoc s.currentInstructions inst})

finish :: (MonadState FromCoreState m) => Terminator -> m ()
finish terminator = do
  modify
    ( \s ->
        s
          { previousBlocks =
              DList.snoc
                s.previousBlocks
                Block
                  { name = s.currentName
                  , params = s.currentParams
                  , instructions = DList.toList s.currentInstructions
                  , terminator
                  }
          , currentName = "unnamed"
          , currentParams = mempty
          , currentInstructions = mempty
          }
    )

start :: (MonadState FromCoreState m) => Text -> [Var] -> m Label
start name params = do
  modify (\s -> s{currentName = name, currentParams = params})
  pure $ Label name

freshTermVar ::
  (MonadVar m, MonadState FromCoreState m) =>
  Type Var ->
  m Var
freshTermVar ty = do
  var <- Metis.SSA.Var.freshVar
  modify (\s -> s{varTypes = HashMap.insert var ty s.varTypes})
  pure var

fromCoreExpr ::
  ( MonadVar m
  , MonadReader FromCoreEnv m
  , MonadState FromCoreState m
  , MonadFix m
  ) =>
  (ty -> Var) ->
  (tm -> Var) ->
  Core.Expr ty tm ->
  m Simple
fromCoreExpr tyVar tmVar expr =
  case expr of
    Core.Var var ->
      pure . Var $ tmVar var
    Core.Name name ->
      pure $ Name name
    Core.Literal lit ->
      pure $ Literal lit
    Core.Add ty a b -> do
      a' <- fromCoreExpr tyVar tmVar a
      b' <- fromCoreExpr tyVar tmVar b
      let !ty' = fmap tyVar ty
      var <- freshTermVar ty'
      emit $ LetC var ty' (Binop Add a' b')
      pure $ Var var
    Core.Subtract ty a b -> do
      a' <- fromCoreExpr tyVar tmVar a
      b' <- fromCoreExpr tyVar tmVar b
      let !ty' = fmap tyVar ty
      var <- freshTermVar ty'
      emit $ LetC var ty' (Binop Subtract a' b')
      pure $ Var var
    Core.Let _ _ ty value rest -> do
      value' <- fromCoreExpr tyVar tmVar value
      var <-
        case value' of
          Var var ->
            pure var
          _ -> do
            let ty' = fmap tyVar ty
            var <- freshTermVar ty'
            emit $ LetS var ty' value'
            pure var
      fromCoreExpr tyVar (unvar (\() -> var) tmVar) $ fromScope rest
    Core.IfThenElse ty cond a b -> do
      cond' <- fromCoreExpr tyVar tmVar cond
      rec finish (IfThenElse cond' thenLabel elseLabel)

          thenLabel <- start "then" []
          a' <- fromCoreExpr tyVar tmVar a
          finish $ Jump afterLabel a'

          elseLabel <- start "else" []
          b' <- fromCoreExpr tyVar tmVar b
          finish $ Jump afterLabel b'

          let !ty' = fmap tyVar ty
          var <- freshTermVar ty'
          afterLabel <- start "after" [var]
      pure $ Var var
    Core.Call _ty f tyArgs args -> do
      f' <- fromCoreExpr tyVar tmVar f

      fTy <- do
        nameTypes <- asks (.nameTypes)
        varTypes <- gets (.varTypes)
        pure . Either.fromRight undefined $ typeOf (const $ error "no varKinds") (fmap absurd . nameTypes) (varTypes HashMap.!) f'

      let (argTyInfos, retTyInfo) = calledFunctionType Type.Var fTy ((fmap . fmap) tyVar tyArgs)

      tyArgs' <- for tyArgs $ \tyArg -> do
        tyArg' <- fromCoreType tyVar tyArg
        case tyArg' of
          Var var ->
            pure var
          _ -> do
            let varType = Type.Ptr Type.Unknown
            var <- freshTermVar varType
            emit $ LetS var varType tyArg'
            pure var

      when (length args /= length argTyInfos) . error $
        "calling function with wrong number of arguments. expected "
          <> show (length argTyInfos)
          <> ", got "
          <> show (length args)
      args' <- for (zip args argTyInfos) $ \(arg, argTyInfo) -> do
        arg' <- fromCoreExpr tyVar tmVar arg
        case arg' of
          Var var ->
            pure var
          _ -> do
            let argTy = argTyInfo.type_
            var <- freshTermVar argTy
            if argTyInfo.byReference
              then do
                emit $ LetC var (Type.Ptr argTy) (Alloca argTy)
                var' <- freshTermVar Type.Unit
                emit $ LetC var' Type.Unit (Store (Var var) arg')
              else emit $ LetS var argTy arg'
            pure var

      let retTy = retTyInfo.type_
      dest <-
        if retTyInfo.byReference
          then do
            var <- freshTermVar retTy
            emit $ LetC var (Type.Ptr retTy) (Alloca retTy)
            pure [var]
          else pure []

      (var, varTy) <-
        if retTyInfo.byReference
          then do
            let varTy = Type.Ptr retTy
            var <- freshTermVar varTy
            pure (var, varTy)
          else do
            var <- freshTermVar retTy
            pure (var, retTy)
      emit $ LetC var varTy (Call f' $ tyArgs' <> args' <> dest)

      if retTyInfo.byReference
        then do
          var' <- freshTermVar retTy
          emit $ LetC var' retTy (Load $ Var var)
          pure $ Var var'
        else pure $ Var var

data CallTypeInfo = CallTypeInfo {type_ :: Type Var, byReference :: Bool}
  deriving (Eq, Show)

calledFunctionType ::
  (a -> Type Var) ->
  Type a ->
  [Type Var] ->
  ([CallTypeInfo], CallTypeInfo)
calledFunctionType f ty tyArgs =
  case ty of
    Type.Forall tyParams rest ->
      let tyParamCount = length tyParams
          (prefix, tyArgs') = splitAt tyParamCount tyArgs
       in calledFunctionType (unvar (\index -> prefix !! fromIntegral @Word64 @Int index) f) (fromScope rest) tyArgs'
    Type.Fn argTys retTy ->
      let
        argTys' = fmap (>>= f) argTys
        retTy' = retTy >>= f
        !b = byReference retTy' retTy
       in
        ( zipWith (\argTy argTy' -> CallTypeInfo{type_ = argTy', byReference = byReference argTy' argTy}) argTys argTys'
        , CallTypeInfo{type_ = retTy', byReference = b}
        )
    _ ->
      let
        ty' = ty >>= f
        !b = byReference ty' ty
       in
        ([], CallTypeInfo{type_ = ty', byReference = b})
  where
    byReference :: Type Var -> Type a -> Bool
    byReference instantiated original =
      case (instantiated, original) of
        (Type.Var{}, Type.Var{}) -> False
        (_, Type.Var{}) -> True
        _ -> False

fromCoreType ::
  (MonadVar m, MonadState FromCoreState m, MonadFix m) =>
  (ty -> Var) ->
  Type ty ->
  m Simple
fromCoreType tyVar ty = do
  let !ty' = fmap tyVar ty
  pure $ Type ty'