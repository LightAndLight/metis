{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Metis.InstSelectionNew (
  InstSelState (..),
  Var (..),
  instSelection_X86_64,
) where

import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.Writer.Class (MonadWriter, tell)
import Data.DList (DList)
import Data.Int (Int64)
import Data.Word (Word64)
import Metis.IsaNew (Address (..), AddressBase (..), Immediate (..), Instruction, Isa, Register, Symbol (..), addOffset, framePointerRegister)
import Metis.IsaNew.X86_64 (Instruction (..), X86_64)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.SSA (Simple)
import qualified Metis.SSA as SSA
import Metis.SSA.Var (MonadVar, freshVar)
import qualified Metis.SSA.Var as SSA (Var)
import qualified Metis.Type as Type

data InstSelState = InstSelState {stackFrameTop :: Int64}

data Var isa
  = Virtual SSA.Var
  | Physical (Register isa)

allocLocal :: forall isa m. (Isa isa, MonadState InstSelState m) => Word64 -> m (Address (Var isa))
allocLocal size = do
  stackFrameTop <- gets (.stackFrameTop)
  let nextStackFrameTop = stackFrameTop - fromIntegral @Word64 @Int64 size
  modify (\s -> s{stackFrameTop = nextStackFrameTop})
  pure Address{base = BaseVar . Physical $ framePointerRegister @isa, offset = nextStackFrameTop}

data Value isa
  = ValueImmediate Immediate
  | ValueVar (Var isa)

instSelection_X86_64 ::
  ( MonadVar m
  , MonadState InstSelState m
  , MonadWriter (DList (Instruction X86_64 (Var X86_64))) m
  ) =>
  SSA.Instruction ->
  m SSA.Var
instSelection_X86_64 inst =
  case inst of
    SSA.LetS var _ty value -> do
      case value of
        SSA.Var src ->
          tell [Mov_rr (Virtual var) (Virtual src)]
        SSA.Name name ->
          tell [Lea_rs (Virtual var) (Symbol name)]
        SSA.Literal lit ->
          tell [Mov_ri (Virtual var) (literalToImmediate lit)]
        SSA.Type{} ->
          error "TODO: instSelection/LetS/Type"
      pure var
    SSA.LetC var _ty operation -> do
      case operation of
        SSA.Binop op a b -> do
          a' <- simpleToVar a
          case (op, simpleToValue b) of
            (SSA.Add, b') ->
              case b' of
                ValueImmediate b'' ->
                  tell [Add_ri (Virtual var) (Virtual a') b'']
                ValueVar b'' ->
                  tell [Add_rr (Virtual var) (Virtual a') b'']
            (SSA.Subtract, b') ->
              case b' of
                ValueImmediate b'' ->
                  tell [Sub_ri (Virtual var) (Virtual a') b'']
                ValueVar b'' ->
                  tell [Sub_rr (Virtual var) (Virtual a') b'']
        SSA.Call f xs -> do
          _ <- error "TODO: instSelection/LetC/CAll" xs
          case f of
            SSA.Var src ->
              tell [Call_r (Virtual src)]
            SSA.Name name ->
              tell [Call_s (Symbol name)]
            SSA.Literal lit ->
              error $ "can't call literal: " <> show lit
            SSA.Type t ->
              error $ "can't call type: " <> show t
        SSA.Alloca t -> do
          addr <- allocLocal @X86_64 $ Type.sizeOf t
          tell [Lea_rm (Virtual var) addr]
        SSA.Store ptr value -> do
          let ptr' = simpleToAddress ptr
          case simpleToValue value of
            ValueImmediate i ->
              tell [Mov_mi ptr' i]
            ValueVar v ->
              tell [Mov_mr ptr' v]
        SSA.Load ptr -> do
          let ptr' = simpleToAddress ptr
          tell [Mov_rm (Virtual var) ptr']
        SSA.GetTypeDictField ptr field -> do
          let ptr' = simpleToAddress ptr
          tell [Mov_rm (Virtual var) (ptr' `addOffset` SSA.typeDictFieldOffset field)]
      pure var

literalToImmediate :: Literal -> Immediate
literalToImmediate l =
  case l of
    Literal.Uint64 w -> Word64 w
    Literal.Bool b -> if b then Word64 1 else Word64 0

simpleToValue :: Simple -> Value isa
simpleToValue simple =
  case simple of
    SSA.Var var ->
      ValueVar $ Virtual var
    SSA.Name name ->
      ValueImmediate . Label $ Symbol name
    SSA.Literal lit ->
      ValueImmediate $ literalToImmediate lit
    SSA.Type _ty ->
      error "TODO: simpleToValue/Type"

simpleToVar ::
  ( MonadVar m
  , MonadWriter (DList (Instruction X86_64 (Var X86_64))) m
  ) =>
  Simple ->
  m SSA.Var
simpleToVar simple =
  case simple of
    SSA.Var var ->
      pure var
    SSA.Name name -> do
      var <- freshVar
      tell [Lea_rs (Virtual var) (Symbol name)]
      pure var
    SSA.Literal lit -> do
      var <- freshVar
      tell [Mov_ri (Virtual var) (literalToImmediate lit)]
      pure var
    SSA.Type _ty ->
      error "TODO: simpleToVar/Type"

simpleToAddress :: Simple -> Address (Var isa)
simpleToAddress simple =
  case simple of
    SSA.Var src ->
      Address{base = BaseVar (Virtual src), offset = 0}
    SSA.Name name ->
      Address{base = BaseLabel $ Symbol name, offset = 0}
    SSA.Literal lit ->
      error $ "literal is not an address: " <> show lit
    SSA.Type _ty ->
      error "TODO: simpleToAddress/Type"