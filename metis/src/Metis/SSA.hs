{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

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
  Function (..),
  FromCoreEnv (..),
  FromCoreState (..),
  initialFromCoreState,
  FromCoreT,
  toBlocks,
  fromCoreExpr,
  fromCoreType,
  fromCoreFunction,

  -- * Internals
  InstantiateTypeInfo (..),
  Polymorphism (..),
  instantiateType,
) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (StateT, evalStateT, runStateT)
import Data.DList (DList)
import qualified Data.DList as DList
import qualified Data.Either as Either
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
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

newtype Label = Label {value :: Text}
  deriving (Eq, Show, Hashable)

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
  modify (\s -> (s :: FromCoreState){varTypes = HashMap.insert var ty s.varTypes})
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

      let (argTyInfos, retTyInfo) = instantiateType Type.Var fTy ((fmap . fmap) tyVar tyArgs)

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
            case argTyInfo.polymorphism of
              Poly{wasMonomorphised = True} -> do
                emit $ LetC var (Type.Ptr argTy) (Alloca argTy)
                var' <- freshTermVar Type.Unit
                emit $ LetC var' Type.Unit (Store (Var var) arg')
              _ ->
                emit $ LetS var argTy arg'
            pure var

      let retTy = retTyInfo.type_
      case retTyInfo.polymorphism of
        Poly{wasMonomorphised = True} -> do
          dest <- freshTermVar retTy
          emit $ LetC dest (Type.Ptr retTy) (Alloca retTy)

          var <- freshTermVar $ Type.Ptr retTy
          emit $ LetC var (Type.Ptr retTy) (Call f' $ tyArgs' <> args' <> [dest])

          var' <- freshTermVar retTy
          emit $ LetC var' retTy (Load $ Var var)

          pure $ Var var'
        _ -> do
          var <- freshTermVar retTy
          emit $ LetC var retTy (Call f' $ tyArgs' <> args')

          pure $ Var var

data Polymorphism = Mono | Poly {wasMonomorphised :: Bool}
  deriving (Eq, Show)

data InstantiateTypeInfo = InstantiateTypeInfo {type_ :: Type Var, polymorphism :: Polymorphism}
  deriving (Eq, Show)

instantiateType ::
  (a -> Type Var) ->
  Type a ->
  [Type Var] ->
  ([InstantiateTypeInfo], InstantiateTypeInfo)
instantiateType f ty tyArgs =
  case ty of
    Type.Forall tyParams rest ->
      let tyParamCount = length tyParams
          (prefix, tyArgs') = splitAt tyParamCount tyArgs
       in instantiateType (unvar (\index -> prefix !! fromIntegral @Word64 @Int index) f) (fromScope rest) tyArgs'
    Type.Fn argTys retTy ->
      case tyArgs of
        [] ->
          let
            argTys' = fmap (>>= f) argTys
            retTy' = retTy >>= f
            !p = getPolymorphism retTy' retTy
           in
            ( zipWith (\argTy argTy' -> InstantiateTypeInfo{type_ = argTy', polymorphism = getPolymorphism argTy' argTy}) argTys argTys'
            , InstantiateTypeInfo{type_ = retTy', polymorphism = p}
            )
        _ ->
          error $ "left over type arguments: " <> show tyArgs
    _ ->
      let
        ty' = ty >>= f
        !p = getPolymorphism ty' ty
       in
        ([], InstantiateTypeInfo{type_ = ty', polymorphism = p})
  where
    getPolymorphism :: Type Var -> Type a -> Polymorphism
    getPolymorphism instantiated original =
      case (instantiated, original) of
        (Type.Var{}, Type.Var{}) -> Poly{wasMonomorphised = False}
        (_, Type.Var{}) -> Poly{wasMonomorphised = True}
        _ -> Mono

fromCoreType ::
  (MonadVar m, MonadState FromCoreState m, MonadFix m) =>
  (ty -> Var) ->
  Type ty ->
  m Simple
fromCoreType tyVar ty = do
  let !ty' = fmap tyVar ty
  pure $ Type ty'

data Function = Function
  { name :: Text
  , args :: [(Var, Type Var)]
  , retTy :: Type Var
  , blocks :: [Block]
  , varTypes :: HashMap Var (Type Var)
  }
  deriving (Eq, Show)

fromCoreFunction :: (MonadFix m, MonadVar m) => (Text -> Type Void) -> Core.Function -> m Function
fromCoreFunction nameTypes function =
  flip evalStateT initialFromCoreState . flip runReaderT FromCoreEnv{nameTypes} $ do
    tyArgs' <- for function.tyArgs $ \(_name, _kind) -> do
      let varTy = Type.Ptr Type.Unknown
      var <- freshTermVar varTy
      pure (var, varTy)

    let (argInfos, retInfo) =
          instantiateType
            Type.Var
            (Type.forall_ function.tyArgs $ Type.Fn (fmap snd function.args) function.retTy)
            (fmap (Type.Var . fst) tyArgs')

    args' <- for argInfos $ \argInfo -> do
      let ty' = argInfo.type_
      let varTy = case argInfo.polymorphism of Poly{} -> Type.Ptr ty'; Mono -> ty'
      var <- freshTermVar varTy
      pure (var, varTy)

    (mDest, retTy) <- do
      let retTy = retInfo.type_
      case retInfo.polymorphism of
        Poly{} -> do
          let varTy = Type.Ptr retTy
          var <- freshTermVar varTy
          pure (Just var, varTy)
        Mono ->
          pure (Nothing, retTy)

    _ <- start "start" []

    body' <-
      fromCoreExpr
        (\index -> fst $ tyArgs' !! fromIntegral @Word64 @Int index)
        (\index -> fst $ args' !! fromIntegral @Word64 @Int index)
        function.body

    terminator <-
      case mDest of
        Just dest -> do
          dict <-
            case retInfo.type_ of
              Type.Var var ->
                pure var
              _ ->
                undefined

          let moveTy = Type.Fn [Type.Ptr Type.Unknown, retTy, retTy] retTy
          var <- freshTermVar moveTy
          emit $ LetC var moveTy (GetTypeDictField (Var dict) TypeDictMove)

          src <-
            case body' of
              Var src ->
                pure src
              _ -> do
                src <- freshTermVar retTy
                emit $ LetS src retTy body'
                pure src

          var' <- freshTermVar retTy
          emit $ LetC var' retTy (Call (Var var) [dict, src, dest])

          pure . Return $ Var var'
        Nothing ->
          pure $ Return body'

    previousBlocks <- gets (.previousBlocks)
    currentName <- gets (.currentName)
    currentParams <- gets (.currentParams)
    currentInstructions <- gets (.currentInstructions)
    varTypes <- gets (.varTypes)

    pure
      Function
        { name = function.name
        , args = tyArgs' <> args' <> foldMap (\dest -> [(dest, retTy)]) mDest
        , retTy
        , blocks =
            DList.toList $
              DList.snoc
                previousBlocks
                Block
                  { name = currentName
                  , params = currentParams
                  , instructions = DList.toList currentInstructions
                  , terminator
                  }
        , varTypes
        }

newtype FromCoreT m a = FromCoreT (ReaderT FromCoreEnv (StateT FromCoreState m) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadReader FromCoreEnv, MonadState FromCoreState, MonadVar)

toBlocks ::
  (Monad m) =>
  FromCoreEnv ->
  Text ->
  FromCoreT m Simple ->
  m (HashMap Var (Type Var), [Block])
toBlocks env blockName (FromCoreT ma) = do
  (simple, s) <- flip runStateT initialFromCoreState{currentName = blockName} $ runReaderT ma env
  pure
    ( s.varTypes
    , DList.toList $
        DList.snoc
          s.previousBlocks
          Block
            { name = s.currentName
            , params = s.currentParams
            , instructions = DList.toList s.currentInstructions
            , terminator = Return simple
            }
    )