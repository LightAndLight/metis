{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.Codegen (printInstruction_X86_64, printInstructions_X86_64) where

import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Metis.Isa (Immediate (..), Isa (..), Memory (..), Symbol (..))
import Metis.Isa.X86_64 (Inst2 (..), Instruction (..), X86_64)

printRegister :: (Isa isa) => Register isa -> Builder
printRegister reg = "%" <> Builder.fromText (registerName reg)

printImmediate :: Immediate -> Builder
printImmediate (Imm i) = "$" <> Builder.fromString (show i)

printMemory :: (Isa isa) => Memory isa -> Builder
printMemory Mem{base, offset} = Builder.fromString (show offset) <> "(" <> printRegister base <> ")"

printSymbol :: Symbol -> Builder
printSymbol sym = Builder.fromText sym.value

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
    Inst2_ir inst2 imm reg ->
      printInst2 inst2 <> " " <> printImmediate imm <> ", " <> printRegister reg
    Inst2_im inst2 imm mem ->
      printInst2 inst2 <> " " <> printImmediate imm <> ", " <> printMemory mem
    Inst2_rr inst2 reg1 reg2 ->
      printInst2 inst2 <> " " <> printRegister reg1 <> ", " <> printRegister reg2
    Inst2_rm inst2 reg mem ->
      printInst2 inst2 <> " " <> printRegister reg <> ", " <> printMemory mem
    Inst2_mr inst2 mem reg ->
      printInst2 inst2 <> " " <> printMemory mem <> ", " <> printRegister reg
    Lea_mr mem reg ->
      "lea " <> printMemory mem <> ", " <> printRegister reg
    Lea_sr sym reg ->
      "lea " <> printSymbol sym <> ", " <> printRegister reg
  where
    printInst2 :: Inst2 -> Builder
    printInst2 inst2 =
      case inst2 of
        Mov -> "mov"
        Add -> "add"
        Sub -> "sub"
        Xor -> "xor"