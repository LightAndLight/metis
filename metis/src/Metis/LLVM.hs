{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module Metis.LLVM (llvmExpr, llvmFunction, llvmType, TypeDicts (..), llvmTypeDicts) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (Var (..), unvar)
import Control.Monad (forM)
import Control.Monad.Fix (MonadFix)
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void (Void, absurd)
import Data.Word (Word64)
import LLVM.AST (Definition (..))
import LLVM.AST.Constant (Constant (..))
import LLVM.AST.Global (Global (..), Parameter (..), functionDefaults)
import LLVM.AST.Name (Name)
import LLVM.AST.Operand (Operand (..))
import LLVM.AST.Type (Type (..), i1, i64, i8, ptr, void)
import LLVM.IRBuilder.Constant (bit, int32, int64)
import LLVM.IRBuilder.Instruction (add, alloca, bitcast, br, call, condBr, gep, load, phi, ret, retVoid, store, sub)
import LLVM.IRBuilder.Module (MonadModuleBuilder, ParameterName (..), emitDefn, global, typedef)
import LLVM.IRBuilder.Monad (IRBuilderT, MonadIRBuilder, block, emptyIRBuilder, fresh, named, runIRBuilderT)
import qualified Metis.Core as Core
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import qualified Metis.Type as Core (Type)
import qualified Metis.Type as Core.Type (Type (..))

llvmExpr ::
  (MonadModuleBuilder m, MonadIRBuilder m, MonadFix m) =>
  (Text -> Core.Type ty) ->
  (tm -> Core.Type ty) ->
  (ty -> Kind) ->
  TypeDicts ->
  (Text -> Operand) ->
  (ty -> Operand) ->
  (tm -> Operand) ->
  Core.Expr ty tm ->
  m Operand
llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand expr =
  case expr of
    Core.Var v ->
      pure $ varOperand v
    Core.Name n ->
      pure $ nameOperand n
    Core.Literal l ->
      pure $ llvmLiteral l
    Core.Add _ a b -> do
      a' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand a
      b' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand b
      add a' b'
    Core.Subtract _ a b -> do
      a' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand a
      b' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand b
      sub a' b'
    Core.Let _ _ valueTy value body -> do
      value' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand value
      llvmExpr nameTy (unvar (\() -> valueTy) varTy) tyKind typeDicts nameOperand tyOperand (unvar (\() -> value') varOperand) (fromScope body)
    Core.IfThenElse _ cond t e -> do
      cond' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand cond
      rec condBr cond' ifTrue ifFalse
          ifTrue <- block
          t' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand t
          br after

          ifFalse <- block
          e' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand e

          br after
          after <- block
      phi [(t', ifTrue), (e', ifFalse)]
    Core.Call _ty f tyArgs args -> do
      let fTy = Core.typeOf nameTy varTy f
      f' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand f
      tyArgs' <- traverse (llvmTypeArg typeDicts tyOperand) tyArgs
      (argTys, retTy) <-
        case fTy of
          Core.Type.Fn argTys retTy ->
            pure (fmap F <$> argTys, F <$> retTy)
          Core.Type.Forall _tyArgKinds (fromScope -> Core.Type.Fn argTys retTy) ->
            pure (argTys, retTy)
          _ ->
            error "can't call non-function type"
      args' <-
        traverse
          ( \(arg, argTy) -> do
              arg' <- llvmExpr nameTy varTy tyKind typeDicts nameOperand tyOperand varOperand arg
              case argTy of
                Core.Type.Var (B index) -> do
                  argRef <- alloca (llvmType tyKind typeDicts.type_ $ tyArgs !! fromIntegral @Word64 @Int index) Nothing 1
                  store argRef 1 arg'
                  bitcast argRef (ptr i8 {- void -})
                _ ->
                  pure arg'
          )
          (zip args argTys)
      destination <-
        case retTy of
          Core.Type.Var (B index) -> do
            let resultTy = llvmType tyKind typeDicts.type_ $ tyArgs !! fromIntegral @Word64 @Int index
            op <- alloca resultTy Nothing 1
            op' <- bitcast op (ptr i8 {- void -})
            pure [(op', [])]
          _ -> pure []
      result <- call f' $ destination <> fmap (,[]) (tyArgs' <> args')
      case retTy of
        Core.Type.Var (B index) -> do
          let resultTy = llvmType tyKind typeDicts.type_ $ tyArgs !! fromIntegral @Word64 @Int index
          typedResult <- bitcast result (ptr resultTy)
          load typedResult 1
        _ -> pure result

llvmTypeArg :: (Monad m) => TypeDicts -> (ty -> Operand) -> Core.Type ty -> m Operand
llvmTypeArg typeDicts tyOperand ty =
  case ty of
    Core.Type.Var a ->
      pure $ tyOperand a
    Core.Type.Uint64 ->
      pure typeDicts.uint64
    Core.Type.Bool ->
      pure typeDicts.bool
    Core.Type.Fn{} ->
      pure typeDicts.ptr
    Core.Type.Forall{} ->
      pure typeDicts.ptr
    Core.Type.Ptr _inner ->
      pure typeDicts.ptr
    Core.Type.Unit ->
      pure typeDicts.unit
    Core.Type.Unknown ->
      error "TODO: Unknown"

llvmType :: (ty -> Kind) -> Type -> Core.Type ty -> Type
llvmType tyKind typeDict ty =
  case ty of
    Core.Type.Var _a ->
      ptr i8 {- void -}
    Core.Type.Uint64 ->
      i64
    Core.Type.Bool ->
      i1
    Core.Type.Fn args retTy ->
      FunctionType
        { resultType = llvmType tyKind typeDict retTy
        , argumentTypes = fmap (llvmType tyKind typeDict) args
        , isVarArg = False
        }
    Core.Type.Forall tyArgs (fromScope -> Core.Type.Fn args retTy) ->
      let tyKind' = unvar (\index -> snd $ tyArgs !! fromIntegral @Word64 @Int index) tyKind
       in FunctionType
            { resultType = llvmType tyKind' typeDict retTy
            , argumentTypes = fmap (const $ ptr i8 {- void -}) tyArgs <> fmap (llvmType tyKind' typeDict) args
            , isVarArg = False
            }
    Core.Type.Forall tyArgs (fromScope -> body) ->
      FunctionType
        { resultType = llvmType (unvar (\index -> snd $ tyArgs !! fromIntegral @Word64 @Int index) tyKind) typeDict body
        , argumentTypes = fmap (const $ ptr i8 {- void -}) tyArgs
        , isVarArg = False
        }
    Core.Type.Ptr inner ->
      ptr $ llvmType tyKind typeDict inner
    Core.Type.Unit ->
      StructureType{isPacked = True, elementTypes = []}
    Core.Type.Unknown ->
      error "TODO: Unknown"

llvmLiteral :: Literal -> Operand
llvmLiteral lit =
  case lit of
    Literal.Uint64 n ->
      int64 (fromIntegral n)
    Literal.Bool b ->
      if b then bit 1 else bit 0

-- Taken from <https://github.com/llvm-hs/llvm-hs/blob/5bca2c1a2a3aa98ecfb19181e7a5ebbf3e212b76/llvm-hs-pure/src/LLVM/IRBuilder/Module.hs>
function ::
  (MonadModuleBuilder m) =>
  -- | Function name
  Name ->
  -- | Parameter types and name suggestions
  [(Type, ParameterName)] ->
  -- | Return type
  Type ->
  -- | Function body builder
  ([Operand] -> IRBuilderT m ()) ->
  m Constant
function label argtys retty body = do
  let tys = fst <$> argtys
  (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
    paramNames <- forM argtys $ \(_, paramName) -> case paramName of
      NoParameterName -> fresh
      ParameterName p -> fresh `named` p
    body $ zipWith LocalReference tys paramNames
    return paramNames
  let
    def =
      GlobalDefinition
        functionDefaults
          { name = label
          , parameters = (zipWith (\ty nm -> Parameter ty nm []) tys paramNames, False)
          , returnType = retty
          , basicBlocks = blocks
          }
    funty = ptr $ FunctionType retty (fst <$> argtys) False
  emitDefn def
  pure $ GlobalReference funty label

data TypeDicts = TypeDicts
  { type_ :: Type
  , uint64 :: Operand
  , bool :: Operand
  , ptr :: Operand
  , unit :: Operand
  }

copyFnType :: Type
copyFnType =
  ptr
    FunctionType
      { resultType = void
      , argumentTypes =
          -- from
          [ ptr i8 -- void
          , -- to
            ptr i8 -- void
          ]
      , isVarArg = False
      }

callTypeDictCopy :: forall m. (MonadModuleBuilder m, MonadIRBuilder m) => Operand -> Operand -> Operand -> m ()
callTypeDictCopy dict from to = do
  fnLocation <- gep dict [int32 0, int32 1]
  fn <- load fnLocation 1
  _ <- call fn [(from, []), (to, [])]
  pure ()

llvmTypeDicts :: (MonadModuleBuilder m) => m TypeDicts
llvmTypeDicts = do
  typeDict <- do
    typedef "TypeDict" . Just $
      StructureType
        { isPacked = False
        , elementTypes =
            -- size
            [ i64
            , copyFnType
            ]
        }

  uint64 <- do
    let ty = i64
    let size = Int{integerBits = 64, integerValue = 8}
    copy <- function "Type_Uint64_copy" [(ptr i8 {- void -}, "from"), (ptr i8 {- void -}, "to")] void $ \case
      [from, to] -> do
        from' <- bitcast from (ptr ty)
        to' <- bitcast to (ptr ty)
        value <- load from' 1
        store to' 1 value
        retVoid
      _ -> undefined

    global
      "Type_Uint64"
      typeDict
      Struct
        { structName = Nothing
        , isPacked = False
        , memberValues =
            [ size
            , copy
            ]
        }

  bool <- do
    let ty = i1
    let size = Int{integerBits = 64, integerValue = 1}
    copy <- function "Type_Bool_copy" [(ptr i8 {- void -}, "from"), (ptr i8 {- void -}, "to")] void $ \case
      [from, to] -> do
        from' <- bitcast from (ptr ty)
        to' <- bitcast to (ptr ty)
        value <- load from' 1
        store to' 1 value
        retVoid
      _ -> undefined

    global
      "Type_Bool"
      typeDict
      Struct
        { structName = Nothing
        , isPacked = False
        , memberValues =
            [ size
            , copy
            ]
        }

  ptrDict <- do
    let ty = ptr i8 -- void
    -- Pointers won't always be 8 bytes.
    let size = Int{integerBits = 64, integerValue = 8}
    copy <- function "Type_Ptr_copy" [(ptr i8 {- void -}, "from"), (ptr i8 {- void -}, "to")] void $ \case
      [from, to] -> do
        from' <- bitcast from (ptr ty)
        to' <- bitcast to (ptr ty)
        value <- load from' 1
        store to' 1 value
        retVoid
      _ -> undefined

    global
      "Type_Ptr"
      typeDict
      Struct
        { structName = Nothing
        , isPacked = False
        , memberValues =
            [ size
            , copy
            ]
        }

  unit <- do
    let size = Int{integerBits = 64, integerValue = 0}
    copy <- function "Type_Unit_copy" [(ptr i8 {- void -}, "from"), (ptr i8 {- void -}, "to")] void $ \case
      [_from, _to] ->
        retVoid
      _ -> undefined

    global
      "Type_Unit"
      typeDict
      Struct
        { structName = Nothing
        , isPacked = False
        , memberValues =
            [ size
            , copy
            ]
        }

  pure TypeDicts{type_ = typeDict, uint64, bool, ptr = ptrDict, unit}

llvmFunction ::
  (MonadModuleBuilder m, MonadFix m) =>
  (Text -> Core.Type Void) ->
  TypeDicts ->
  (Text -> Operand) ->
  Core.Function ->
  m Constant
llvmFunction nameTy typeDicts nameOperand Core.Function{name, tyArgs, args, retTy, body} = do
  let tyArgCount = length tyArgs
  let tyKind = \index -> snd $ tyArgs !! fromIntegral @Word64 @Int index
  let
    destination =
      case retTy of
        Core.Type.Var _index ->
          [(ptr i8 {- void -}, "output")]
        _ -> []
    offset = length destination
  function
    (fromString $ Text.unpack name)
    ( destination
        <> fmap (\(argName, _argKind) -> (ptr typeDicts.type_, fromString $ Text.unpack argName)) tyArgs
        <> fmap (\(argName, argTy) -> (llvmType tyKind typeDicts.type_ argTy, fromString $ Text.unpack argName)) args
    )
    (llvmType tyKind typeDicts.type_ retTy)
    $ \llvmArgs -> do
      result <-
        llvmExpr
          (fmap absurd . nameTy)
          (\index -> snd $ args !! fromIntegral @Word64 @Int index)
          tyKind
          typeDicts
          nameOperand
          (\index -> llvmArgs !! (offset + fromIntegral @Word64 @Int index))
          (\index -> llvmArgs !! (offset + tyArgCount + fromIntegral @Word64 @Int index))
          body
      case retTy of
        Core.Type.Var index -> do
          let tyArg = llvmArgs !! (offset + fromIntegral @Word64 @Int index)
          let dest = head llvmArgs
          _ <- callTypeDictCopy tyArg result dest
          ret dest
        _ ->
          ret result