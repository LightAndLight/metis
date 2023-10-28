{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module Metis.LLVM (llvmExpr, TypeDicts (..), llvmTypeDicts) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad (forM)
import Control.Monad.Fix (MonadFix)
import Data.Text (Text)
import LLVM.AST (Definition (..))
import LLVM.AST.Constant (Constant (..))
import LLVM.AST.Global (Global (..), Parameter (..), functionDefaults)
import LLVM.AST.Name (Name)
import LLVM.AST.Operand (Operand (..))
import LLVM.AST.Type (Type (..), i1, i64, i8, ptr, void)
import LLVM.IRBuilder.Constant (bit, int64)
import LLVM.IRBuilder.Instruction (add, bitcast, call, condBr, load, phi, retVoid, store, sub)
import LLVM.IRBuilder.Module (MonadModuleBuilder, ParameterName (..), emitDefn, global, typedef)
import LLVM.IRBuilder.Monad (IRBuilderT, MonadIRBuilder, block, emptyIRBuilder, fresh, named, runIRBuilderT)
import qualified Metis.Core as Core
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import qualified Metis.Type as Core (Type)
import qualified Metis.Type as Core.Type (Type (..))

llvmExpr ::
  (MonadModuleBuilder m, MonadIRBuilder m, MonadFix m) =>
  TypeDicts ->
  (Text -> Operand) ->
  (ty -> Operand) ->
  (tm -> Operand) ->
  Core.Expr ty tm ->
  m Operand
llvmExpr typeDicts nameOperand tyOperand varOperand expr =
  case expr of
    Core.Var v ->
      pure $ varOperand v
    Core.Name n ->
      pure $ nameOperand n
    Core.Literal l ->
      pure $ llvmLiteral l
    Core.Add _ a b -> do
      a' <- llvmExpr typeDicts nameOperand tyOperand varOperand a
      b' <- llvmExpr typeDicts nameOperand tyOperand varOperand b
      add a' b'
    Core.Subtract _ a b -> do
      a' <- llvmExpr typeDicts nameOperand tyOperand varOperand a
      b' <- llvmExpr typeDicts nameOperand tyOperand varOperand b
      sub a' b'
    Core.Let _ _ _ value body -> do
      value' <- llvmExpr typeDicts nameOperand tyOperand varOperand value
      llvmExpr typeDicts nameOperand tyOperand (unvar (\() -> value') varOperand) (fromScope body)
    Core.IfThenElse _ cond t e -> do
      cond' <- llvmExpr typeDicts nameOperand tyOperand varOperand cond
      rec condBr cond' ifTrue ifFalse
          ifTrue <- block
          t' <- llvmExpr typeDicts nameOperand tyOperand varOperand t
          ifFalse <- block
          e' <- llvmExpr typeDicts nameOperand tyOperand varOperand e
      phi [(t', ifTrue), (e', ifFalse)]
    Core.Call _ty f tyArgs args -> do
      f' <- llvmExpr typeDicts nameOperand tyOperand varOperand f
      tyArgs' <- traverse (llvmTypeArg typeDicts tyOperand) tyArgs
      args' <- traverse (llvmExpr typeDicts nameOperand tyOperand varOperand) args
      call f' (fmap (,[]) (tyArgs' <> args'))

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

{-
llvmType :: Core.Type ty -> Type
llvmType ty =
  case ty of
    Core.Type.Var _a ->
      ptr void
    Core.Type.Uint64 ->
      i64
    Core.Type.Bool ->
      i1
    Core.Type.Fn args ret ->
      FunctionType
        { resultType = llvmType ret
        , argumentTypes = fmap llvmType args
        , isVarArg = False
        }
    Core.Type.Forall tyArgs (fromScope -> Core.Type.Fn args ret) ->
      FunctionType
        { resultType = llvmType ret
        , argumentTypes = fmap (const $ ptr void) tyArgs <> fmap llvmType args
        , isVarArg = False
        }
    Core.Type.Forall tyArgs (fromScope -> body) ->
      FunctionType
        { resultType = llvmType body
        , argumentTypes = fmap (const $ ptr void) tyArgs
        , isVarArg = False
        }
    Core.Type.Ptr inner ->
      ptr $ llvmType inner
    Core.Type.Unit ->
      StructureType{isPacked = True, elementTypes = []}
    Core.Type.Unknown ->
      error "TODO: Unknown"
-}

llvmLiteral :: Literal -> Operand
llvmLiteral lit =
  case lit of
    Literal.Uint64 n ->
      int64 (fromIntegral n)
    Literal.Bool b ->
      if b then bit 1 else bit 0

data TypeDicts = TypeDicts
  { uint64 :: Operand
  , bool :: Operand
  , ptr :: Operand
  , unit :: Operand
  }

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

llvmTypeDicts :: (MonadModuleBuilder m) => m TypeDicts
llvmTypeDicts = do
  typeDict <- do
    typedef "TypeDict" . Just $
      StructureType
        { isPacked = False
        , elementTypes =
            -- size
            [ i64
            , -- copy
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

  pure TypeDicts{uint64, bool, ptr = ptrDict, unit}