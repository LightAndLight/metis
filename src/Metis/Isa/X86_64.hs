{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.Isa.X86_64 (X86_64, Register (..), Instruction (..), Inst2 (..)) where

import Metis.Isa (
  Add (..),
  Immediate,
  Isa (..),
  Memory,
  Mov (..),
  Pop (..),
  Push (..),
  Sub (..),
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
    | Inst2_ir Inst2 Immediate (Register X86_64)
    | Inst2_im Inst2 Immediate (Memory X86_64)
    | Inst2_rr Inst2 (Register X86_64) (Register X86_64)
    | Inst2_rm Inst2 (Register X86_64) (Memory X86_64)
    | Inst2_mr Inst2 (Memory X86_64) (Register X86_64)

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

instance Push X86_64 (Register X86_64) where push = Push_r

instance Pop X86_64 (Register X86_64) where pop = Pop_r