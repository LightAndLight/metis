{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.Codegen (
  printInstruction_X86_64,
  printInstructions_X86_64,
  printBlocks_X86_64,
) where

import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Metis.Isa (Immediate (..), Isa (..), Memory (..), Op2 (..), Symbol (..))
import Metis.Isa.X86_64 (Inst2 (..), Instruction (..), X86_64)

printRegister :: (Isa isa) => Register isa -> Builder
printRegister reg = "%" <> Builder.fromText (registerName reg)

printImmediate :: Immediate -> Builder
printImmediate (Imm i) = "$" <> Builder.fromString (show i)

printMemory :: (Isa isa) => Memory isa -> Builder
printMemory Mem{base, offset} = Builder.fromString (show offset) <> "(" <> printRegister base <> ")"

printSymbol :: Symbol -> Builder
printSymbol sym = Builder.fromText sym.value

printBlocks_X86_64 :: [(Symbol, [Instruction X86_64])] -> Builder
printBlocks_X86_64 = foldMap (\(label, instructions) -> printSymbol label <> ":\n" <> printInstructions_X86_64 instructions)

printInstructions_X86_64 :: [Instruction X86_64] -> Builder
printInstructions_X86_64 = foldMap ((<> "\n") . printInstruction_X86_64)

printInstruction_X86_64 :: Instruction X86_64 -> Builder
printInstruction_X86_64 inst =
  case inst of
    Push_r reg ->
      "push " <> printRegister reg
    Pop_r reg ->
      "pop " <> printRegister reg
    Call_s sym ->
      "call " <> printSymbol sym
    Je_s sym ->
      "je " <> printSymbol sym
    Jmp_s sym ->
      "jmp " <> printSymbol sym
    Inst2_ir inst2 op2 ->
      -- AT&T syntax
      printInst2 inst2 <> " " <> printImmediate op2.src <> ", " <> printRegister op2.dest
    Inst2_im inst2 op2 ->
      printInst2 inst2 <> " " <> printImmediate op2.src <> ", " <> printMemory op2.dest
    Inst2_rr inst2 op2 ->
      printInst2 inst2 <> " " <> printRegister op2.src <> ", " <> printRegister op2.dest
    Inst2_rm inst2 op2 ->
      printInst2 inst2 <> " " <> printRegister op2.src <> ", " <> printMemory op2.dest
    Inst2_mr inst2 op2 ->
      printInst2 inst2 <> " " <> printMemory op2.src <> ", " <> printRegister op2.dest
    Lea_mr op2 ->
      "lea " <> printMemory op2.src <> ", " <> printRegister op2.dest
    Lea_sr op2 ->
      "lea " <> printSymbol op2.src <> ", " <> printRegister op2.dest
    Cmp_ri a b ->
      -- In AT&T syntax, `cmp a, b` returns "greater than" when `b > a`.
      -- `Cmp_ri` keeps its arguments in the actual comparison order, so we have to swap the
      -- operands when generating AT&T syntax.
      "cmp " <> printImmediate b <> ", " <> printRegister a
    Cmp_mi a b ->
      "cmp " <> printImmediate b <> ", " <> printMemory a
  where
    printInst2 :: Inst2 -> Builder
    printInst2 inst2 =
      case inst2 of
        Mov -> "mov"
        Add -> "add"
        Sub -> "sub"
        Xor -> "xor"