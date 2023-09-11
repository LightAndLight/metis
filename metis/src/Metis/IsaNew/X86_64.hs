{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.IsaNew.X86_64 (
  X86_64,
  Instruction (..),
  Register (..),
  allocRegisters_X86_64,
) where

import Data.Hashable (Hashable)
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import Metis.IsaNew (Address (..), Immediate, Isa (..), Symbol)
import Metis.RegisterAllocation (AllocRegisters (..), Usage (..), VarInfo {- VarType (..) -} (..))

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