{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.IsaNew.X86_64 (
  X86_64,
  Instruction (..),
  Register (..),
  allocRegisters_X86_64,
) where

import Data.Hashable (Hashable)
import qualified Data.Sequence as Seq
import Data.Word (Word64)
import GHC.Generics (Generic)
import Metis.IsaNew (Address, Immediate, Isa (..), Symbol)
import Metis.RegisterAllocation (AllocRegisters (..), Usage (..), VarInfo (..), VarType (..))

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
    = Push_r (var (Register X86_64))
    | Push_m (Address X86_64)
    | Push_i Immediate
    | Pop_r (var (Register X86_64))
    | Call_s Symbol
    | Call_r (var (Register X86_64))
    | Je_s Symbol
    | Jmp_s Symbol
    | Jmp_r (var (Register X86_64))
    | Jmp_m (Address X86_64)
    | Ret
    | Ret_i Immediate
    | Mov_ri (var (Register X86_64)) Immediate
    | Mov_rr (var (Register X86_64)) (var (Register X86_64))
    | Mov_rm (var (Register X86_64)) (Address X86_64)
    | Mov_mi (Address X86_64) Immediate
    | Mov_mr (Address X86_64) (var (Register X86_64))
    | Lea_rm (var (Register X86_64)) (Address X86_64)
    | Lea_rs (var (Register X86_64)) Symbol
    | Cmp_ri (var (Register X86_64)) Immediate
    | Cmp_mi (Address X86_64) Immediate
    | Add_ri (var (Register X86_64)) (var (Register X86_64)) Immediate
    | Add_rr (var (Register X86_64)) (var (Register X86_64)) (var (Register X86_64))
    | Sub_ri (var (Register X86_64)) (var (Register X86_64)) Immediate
    | Sub_rr (var (Register X86_64)) (var (Register X86_64)) (var (Register X86_64))

instance Hashable (Register X86_64)

deriving instance (forall a. (Eq a) => Eq (var a)) => Eq (Instruction X86_64 var)
deriving instance (forall a. (Show a) => Show (var a)) => Show (Instruction X86_64 var)

allocRegisters_X86_64 :: AllocRegisters X86_64
allocRegisters_X86_64 =
  AllocRegisters
    { traverseVars
    , instructionVarInfo
    , load = Mov_rm
    , store = Mov_mr
    }
  where
    traverseVars ::
      forall m var var'.
      (Applicative m) =>
      (forall a. var a -> m (var' a)) ->
      Instruction X86_64 var ->
      m (Instruction X86_64 var')
    traverseVars f inst =
      case inst of
        Push_r a ->
          Push_r <$> f a
        Push_m a ->
          pure $ Push_m a
        Push_i a ->
          pure $ Push_i a
        Pop_r a ->
          Pop_r <$> f a
        Call_s a ->
          pure $ Call_s a
        Call_r a ->
          Call_r <$> f a
        Je_s a ->
          pure $ Je_s a
        Jmp_s a ->
          pure $ Jmp_s a
        Jmp_r a ->
          Jmp_r <$> f a
        Jmp_m a ->
          pure $ Jmp_m a
        Ret ->
          pure Ret
        Ret_i a ->
          pure $ Ret_i a
        Mov_ri a b ->
          (\a' -> Mov_ri a' b) <$> f a
        Mov_rr a b ->
          Mov_rr <$> f a <*> f b
        Mov_rm a b ->
          (\a' -> Mov_rm a' b) <$> f a
        Mov_mi a b ->
          pure $ Mov_mi a b
        Mov_mr a b ->
          Mov_mr a <$> f b
        Lea_rm a b ->
          (\a' -> Lea_rm a' b) <$> f a
        Lea_rs a b ->
          (\a' -> Lea_rs a' b) <$> f a
        Cmp_ri a b ->
          (\a' -> Cmp_ri a' b) <$> f a
        Cmp_mi a b ->
          pure $ Cmp_mi a b
        Add_ri a b c ->
          (\a' b' -> Add_ri a' b' c) <$> f a <*> f b
        Add_rr a b c ->
          Add_rr <$> f a <*> f b <*> f c
        Sub_ri a b c ->
          (\a' b' -> Sub_ri a' b' c) <$> f a <*> f b
        Sub_rr a b c ->
          Sub_rr <$> f a <*> f b <*> f c

    instructionVarInfo ::
      forall var.
      (forall a. var a -> Word64) ->
      Instruction X86_64 var ->
      Instruction X86_64 (VarInfo X86_64 var)
    instructionVarInfo _varSize inst =
      case inst of
        Push_r a ->
          Push_r (VarInfo (Use []) VarReg a)
        Push_m a ->
          Push_m a
        Push_i a ->
          Push_i a
        Pop_r a ->
          Pop_r (VarInfo (Use []) VarReg a)
        Call_s a ->
          Call_s a
        Call_r a ->
          Call_r (VarInfo (Use []) VarReg a)
        Je_s a ->
          Je_s a
        Jmp_s a ->
          Jmp_s a
        Jmp_r a ->
          Jmp_r (VarInfo (Use []) VarReg a)
        Jmp_m a ->
          Jmp_m a
        Ret ->
          Ret
        Ret_i a ->
          Ret_i a
        Mov_ri a b ->
          Mov_ri (VarInfo DefNew VarReg a) b
        Mov_rr a b ->
          Mov_rr (VarInfo DefNew VarReg a) (VarInfo (Use []) VarReg b)
        Mov_rm a b ->
          Mov_rm (VarInfo DefNew VarReg a) b
        Mov_mi a b ->
          Mov_mi a b
        Mov_mr a b ->
          Mov_mr a (VarInfo (Use []) VarReg b)
        Lea_rm a b ->
          Lea_rm (VarInfo DefNew VarReg a) b
        Lea_rs a b ->
          Lea_rs (VarInfo DefNew VarReg a) b
        Cmp_ri a b ->
          Cmp_ri (VarInfo (Use []) VarReg a) b
        Cmp_mi a b ->
          Cmp_mi a b
        Add_ri a b c ->
          Add_ri (VarInfo (DefReuse b) VarReg a) (VarInfo (Use []) VarReg b) c
        Add_rr a b c ->
          Add_rr (VarInfo (DefReuse b) VarReg a) (VarInfo (Use [c]) VarReg b) (VarInfo (Use [b]) VarReg c)
        Sub_ri a b c ->
          Sub_ri (VarInfo (DefReuse b) VarReg a) (VarInfo (Use []) VarReg b) c
        Sub_rr a b c ->
          Sub_rr (VarInfo (DefReuse b) VarReg a) (VarInfo (Use [c]) VarReg b) (VarInfo (Use [b]) VarReg c)