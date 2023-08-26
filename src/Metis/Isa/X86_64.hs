{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.Isa.X86_64 (X86_64, Register (..), Instruction (..), Inst2 (..)) where

import Metis.Isa (
  Add (..),
  Call (..),
  Cmp (..),
  Immediate,
  Isa (..),
  Je (..),
  Jmp (..),
  Lea (..),
  Memory,
  Mov (..),
  Op2,
  Pop (..),
  Push (..),
  Sub (..),
  Symbol (..),
  Xor (..),
 )

data X86_64

instance Isa X86_64 where
  data Register X86_64
    = Rax
    | Rbx
    | Rcx
    | Rdx
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
    deriving (Eq, Show)

  data Instruction X86_64
    = Push_r (Register X86_64)
    | Pop_r (Register X86_64)
    | Call_s Symbol
    | Je_s Symbol
    | Jmp_s Symbol
    | Inst2_ir Inst2 (Op2 Immediate (Register X86_64))
    | Inst2_im Inst2 (Op2 Immediate (Memory X86_64))
    | Inst2_rr Inst2 (Op2 (Register X86_64) (Register X86_64))
    | Inst2_rm Inst2 (Op2 (Register X86_64) (Memory X86_64))
    | Inst2_mr Inst2 (Op2 (Memory X86_64) (Register X86_64))
    | Lea_mr (Op2 (Memory X86_64) (Register X86_64))
    | Lea_sr (Op2 Symbol (Register X86_64))
    | Cmp_ri (Register X86_64) Immediate
    | Cmp_mi (Memory X86_64) Immediate

  registerName reg =
    case reg of
      Rax -> "rax"
      Rbx -> "rbx"
      Rcx -> "rcx"
      Rdx -> "rdx"
      Rbp -> "rbp"
      Rsp -> "rsp"
      Rsi -> "rsi"
      Rdi -> "rdi"
      R8 -> "r8"
      R9 -> "r9"
      R10 -> "r10"
      R11 -> "r11"
      R12 -> "r12"
      R13 -> "r13"
      R14 -> "r14"
      R15 -> "r15"

  generalPurposeRegisters =
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

data Inst2
  = Mov
  | Add
  | Sub
  | Xor

instance Mov X86_64 Immediate (Register X86_64) where mov = Inst2_ir Mov
instance Mov X86_64 Immediate (Memory X86_64) where mov = Inst2_im Mov
instance Mov X86_64 (Register X86_64) (Register X86_64) where mov = Inst2_rr Mov
instance Mov X86_64 (Register X86_64) (Memory X86_64) where mov = Inst2_rm Mov
instance Mov X86_64 (Memory X86_64) (Register X86_64) where mov = Inst2_mr Mov

instance Add X86_64 Immediate (Register X86_64) where add = Inst2_ir Add
instance Add X86_64 Immediate (Memory X86_64) where add = Inst2_im Add
instance Add X86_64 (Register X86_64) (Register X86_64) where add = Inst2_rr Add
instance Add X86_64 (Register X86_64) (Memory X86_64) where add = Inst2_rm Add
instance Add X86_64 (Memory X86_64) (Register X86_64) where add = Inst2_mr Add

instance Sub X86_64 Immediate (Register X86_64) where sub = Inst2_ir Sub
instance Sub X86_64 Immediate (Memory X86_64) where sub = Inst2_im Sub
instance Sub X86_64 (Register X86_64) (Register X86_64) where sub = Inst2_rr Sub
instance Sub X86_64 (Register X86_64) (Memory X86_64) where sub = Inst2_rm Sub
instance Sub X86_64 (Memory X86_64) (Register X86_64) where sub = Inst2_mr Sub

instance Xor X86_64 Immediate (Register X86_64) where xor = Inst2_ir Xor
instance Xor X86_64 Immediate (Memory X86_64) where xor = Inst2_im Xor
instance Xor X86_64 (Register X86_64) (Register X86_64) where xor = Inst2_rr Xor
instance Xor X86_64 (Register X86_64) (Memory X86_64) where xor = Inst2_rm Xor
instance Xor X86_64 (Memory X86_64) (Register X86_64) where xor = Inst2_mr Xor

instance Lea X86_64 (Memory X86_64) (Register X86_64) where lea = Lea_mr
instance Lea X86_64 Symbol (Register X86_64) where lea = Lea_sr

instance Cmp X86_64 (Register X86_64) Immediate where cmp = Cmp_ri
instance Cmp X86_64 (Memory X86_64) Immediate where cmp = Cmp_mi

instance Push X86_64 (Register X86_64) where push = Push_r

instance Pop X86_64 (Register X86_64) where pop = Pop_r

instance Call X86_64 Symbol where call = Call_s

instance Je X86_64 Symbol where je = Je_s
instance Jmp X86_64 Symbol where jmp = Jmp_s