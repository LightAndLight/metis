{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}

module Test.AllocateRegisters (spec) where

import Control.Monad.State.Class (modify)
import Control.Monad.State.Strict (evalState)
import Data.Sequence as Seq
import Metis.AllocateRegisters (
  AllocateRegistersState (..),
  Location (..),
  RegisterFunctionArgument (..),
  initialAllocateRegistersState,
  moveRegisterFunctionArguments,
 )
import Metis.Asm (BlockAttribute (..))
import Metis.Isa (Isa (generalPurposeRegisters), Op2 (..), mov)
import Metis.Isa.X86_64 (Register (..), X86_64)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.AllocateRegisters" $ do
    describe "moveRegisterFunctionArguments" $ do
      it "{%rbx, %rax} -> {%rax, %rbx}" $ do
        let result = flip evalState (initialAllocateRegistersState (generalPurposeRegisters @X86_64) mempty "main" [Global]) $ do
              modify (\s -> s{available = Seq.filter (`notElem` [Rax, Rbx]) s.available})
              moveRegisterFunctionArguments
                mempty
                [ RegisterFunctionArgument{callerSave = False, size = 8, src = Register Rbx, dest = Rax}
                , RegisterFunctionArgument{callerSave = False, size = 8, src = Register Rax, dest = Rbx}
                ]

        result
          `shouldBe` [ mov Op2{src = Rax, dest = Rcx} -- save destination to temporary
                     , mov Op2{src = Rbx, dest = Rax} -- write value to destination
                     -- `Rax` should now be considered remapped to `Rcx`
                     {- No need to save the final destination to a temporary.
                     , mov Op2{src = Rbx, dest = Rdx} -- save destination to temporary
                     -}
                     , mov Op2{src = Rcx {- Rax remapped -}, dest = Rbx} -- write value to destination
                     ]