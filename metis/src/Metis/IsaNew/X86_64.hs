{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.IsaNew.X86_64 (
  X86_64,
  Instruction (..),
  Register (..),
  allocRegisters_X86_64,
  instSelection_X86_64,
) where

import Control.Monad.State.Class (MonadState)
import Control.Monad.Writer.Class (MonadWriter, tell)
import Data.DList (DList)
import Data.Hashable (Hashable)
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import Metis.InstSelectionNew (InstSelState, Value (..), Var (..))
import qualified Metis.InstSelectionNew as InstSelection
import Metis.IsaNew (Address (..), Immediate (..), Instruction, Isa (..), Register, Symbol (..), addOffset, framePointerRegister)
import Metis.RegisterAllocation (AllocRegisters (..), Usage (..), VarInfo (..))
import Metis.SSA (Simple)
import qualified Metis.SSA as SSA
import Metis.SSA.Var (MonadVar, freshVar)
import qualified Metis.SSA.Var as SSA (Var)
import qualified Metis.Type as Type

data X86_64

instance Isa X86_64 where
  pointerSize = 8

  data Register X86_64
    = Rax
    | Rbx
    | Rcx
    | Rdx
    | Dl
    | Rbp
    | Rsp
    | Rsi
    | Rdi
    | R8
    | R9
    | R10
    | R11
    | R12
    | R13
    | R14
    | R15
    deriving (Eq, Show, Generic)

  registerSize Rax = 8
  registerSize Rbx = 8
  registerSize Rcx = 8
  registerSize Rdx = 8
  registerSize Dl = 1
  registerSize Rbp = 8
  registerSize Rsp = 8
  registerSize Rsi = 8
  registerSize Rdi = 8
  registerSize R8 = 8
  registerSize R9 = 8
  registerSize R10 = 8
  registerSize R11 = 8
  registerSize R12 = 8
  registerSize R13 = 8
  registerSize R14 = 8
  registerSize R15 = 8

  registerName Rax = "rax"
  registerName Rbx = "rbx"
  registerName Rcx = "rcx"
  registerName Rdx = "rdx"
  registerName Dl = "dl"
  registerName Rbp = "rbp"
  registerName Rsp = "rsp"
  registerName Rsi = "rsi"
  registerName Rdi = "rdi"
  registerName R8 = "r8"
  registerName R9 = "r9"
  registerName R10 = "r10"
  registerName R11 = "r11"
  registerName R12 = "r12"
  registerName R13 = "r13"
  registerName R14 = "r14"
  registerName R15 = "r15"

  framePointerRegister = Rbp

  generalPurposeRegisters =
    Seq.fromList
      [ Rax
      , Rbx
      , Rcx
      , Rdx
      , Rsi
      , Rdi
      , R8
      , R9
      , R10
      , R11
      , R12
      , R13
      , R14
      , R15
      ]

  data Instruction X86_64 var
    = Push_r var
    | Push_m (Address var)
    | Push_i Immediate
    | Pop_r var
    | Call_s Symbol
    | Call_r var
    | Je_s Symbol
    | Jmp_s Symbol
    | Jmp_r var
    | Jmp_m (Address var)
    | Ret
    | Ret_i Immediate
    | Mov_ri var Immediate
    | Mov_rr var var
    | Mov_rm var (Address var)
    | Mov_mi (Address var) Immediate
    | Mov_mr (Address var) var
    | Lea_rm var (Address var)
    | Lea_rs var Symbol
    | Cmp_ri var Immediate
    | Cmp_mi (Address var) Immediate
    | Add_ri var var Immediate
    | Add_rr var var var
    | Sub_ri var var Immediate
    | Sub_rr var var var
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance Hashable (Register X86_64)

allocRegisters_X86_64 :: AllocRegisters X86_64
allocRegisters_X86_64 =
  AllocRegisters
    { instructionVarInfo
    , load = Mov_rm
    , store = Mov_mr
    }
  where
    instructionVarInfo ::
      forall var.
      Instruction X86_64 var ->
      Instruction X86_64 (VarInfo var)
    instructionVarInfo inst =
      case inst of
        Push_r a ->
          Push_r (VarInfo (Use []) a)
        Push_m a ->
          Push_m $ fmap (VarInfo (Use [])) a
        Push_i a ->
          Push_i a
        Pop_r a ->
          Pop_r (VarInfo (Use []) a)
        Call_s a ->
          Call_s a
        Call_r a ->
          Call_r (VarInfo (Use []) a)
        Je_s a ->
          Je_s a
        Jmp_s a ->
          Jmp_s a
        Jmp_r a ->
          Jmp_r (VarInfo (Use []) a)
        Jmp_m a ->
          Jmp_m $ fmap (VarInfo (Use [])) a
        Ret ->
          Ret
        Ret_i a ->
          Ret_i a
        Mov_ri a b ->
          Mov_ri (VarInfo DefNew a) b
        Mov_rr a b ->
          Mov_rr (VarInfo DefNew a) (VarInfo (Use []) b)
        Mov_rm a b ->
          Mov_rm (VarInfo DefNew a) (fmap (VarInfo (Use [])) b)
        Mov_mi a b ->
          Mov_mi (fmap (VarInfo (Use [])) a) b
        Mov_mr a b ->
          Mov_mr (fmap (VarInfo (Use [])) a) (VarInfo (Use []) b)
        Lea_rm a b ->
          Lea_rm (VarInfo DefNew a) (fmap (VarInfo (Use [])) b)
        Lea_rs a b ->
          Lea_rs (VarInfo DefNew a) b
        Cmp_ri a b ->
          Cmp_ri (VarInfo (Use []) a) b
        Cmp_mi a b ->
          Cmp_mi (fmap (VarInfo (Use [])) a) b
        Add_ri a b c ->
          Add_ri (VarInfo (DefReuse b) a) (VarInfo (Use []) b) c
        Add_rr a b c ->
          Add_rr (VarInfo (DefReuse b) a) (VarInfo (Use [c]) b) (VarInfo (Use [b]) c)
        Sub_ri a b c ->
          Sub_ri (VarInfo (DefReuse b) a) (VarInfo (Use []) b) c
        Sub_rr a b c ->
          Sub_rr (VarInfo (DefReuse b) a) (VarInfo (Use [c]) b) (VarInfo (Use [b]) c)

instSelection_X86_64 ::
  ( MonadVar m
  , MonadState InstSelState m
  , MonadWriter (DList (Instruction X86_64 (InstSelection.Var X86_64))) m
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
          tell [Mov_ri (Virtual var) (InstSelection.literalToImmediate lit)]
        SSA.Type{} ->
          error "TODO: instSelection/LetS/Type"
      pure var
    SSA.LetC var _ty operation -> do
      case operation of
        SSA.Binop op a b -> do
          a' <- simpleToVar a
          case (op, InstSelection.simpleToValue b) of
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
          addr <- InstSelection.allocLocal @X86_64 $ Type.sizeOf t
          tell [Lea_rm (Virtual var) addr]
        SSA.Store ptr value -> do
          let ptr' = InstSelection.simpleToAddress ptr
          case InstSelection.simpleToValue value of
            ValueImmediate i ->
              tell [Mov_mi ptr' i]
            ValueVar v ->
              tell [Mov_mr ptr' v]
        SSA.Load ptr -> do
          let ptr' = InstSelection.simpleToAddress ptr
          tell [Mov_rm (Virtual var) ptr']
        SSA.GetTypeDictField ptr field -> do
          let ptr' = InstSelection.simpleToAddress ptr
          tell [Mov_rm (Virtual var) (ptr' `addOffset` SSA.typeDictFieldOffset field)]
      pure var

simpleToVar ::
  ( MonadVar m
  , MonadWriter (DList (Instruction X86_64 (InstSelection.Var X86_64))) m
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
      tell [Mov_ri (Virtual var) (InstSelection.literalToImmediate lit)]
      pure var
    SSA.Type _ty ->
      error "TODO: simpleToVar/Type"