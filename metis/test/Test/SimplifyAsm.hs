module Test.SimplifyAsm (spec) where

import Data.Word (Word64)
import Metis.Asm (Statement (..))
import Metis.Isa (Memory (..), MemoryBase (..), Op2 (..), Symbol (..), add, call, imm, lea, load, mov, store, sub)
import Metis.Isa.X86_64 (Inst2 (..), Instruction (..), Register (..), deadCodeElimination_X86_64, propagateConstants_X86_64)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.SimplifyAsm" $ do
    describe "X86_64" $ do
      describe "propagateConstants" $ do
        it "1" $ do
          let input =
                fmap
                  Instruction
                  [ mov Op2{src = Rsp, dest = Rbp}
                  , sub Op2{src = imm (16 :: Word64), dest = Rsp}
                  , -- { }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rax}
                  , -- { rax -> address(-8(%rbp)) }
                    mov Op2{src = imm (99 :: Word64), dest = Rbx}
                  , -- { rax -> address(-8(%rbp)), rbx -> 99 }
                    store Op2{src = Rbx, dest = Mem{base = BaseRegister Rax, offset = 0}}
                  , -- { rax -> address(-8(%rbp)), rbx -> 99, (rax) -> 99 }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rbx}
                  , -- { rax -> address(-8(%rbp)), (rax) -> 99, rbx -> address(-16(%rbp)) }
                    mov Op2{src = Rax, dest = Rcx}
                  , -- { rax -> address(-8(%rbp)), (rax) -> 99, rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)) }
                    mov Op2{src = imm (Symbol "type_Uint64"), dest = Rax}
                  , -- { rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)) }
                    mov Op2{src = Rbx, dest = Rdx}
                  , -- { rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)), rdx -> address(-16(%rbp)) }
                    mov Op2{src = Rcx, dest = Rbx}
                  , -- { rbx -> address(-8(%rbp)), rcx -> address(-8(%rbp)), rdx -> address(-16(%rbp)) }
                    mov Op2{src = Rdx, dest = Rcx}
                  , -- { rbx -> address(-8(%rbp)), rcx -> address(-16(%rbp)), rdx -> address(-16(%rbp)) }
                    call (Symbol "id")
                  , -- { }
                    load Op2{src = Mem{base = BaseRegister Rax, offset = 0}, dest = Rax}
                  , add Op2{src = imm (1 :: Word64), dest = Rax}
                  ]
          let output =
                fmap
                  Instruction
                  [ mov Op2{src = Rsp, dest = Rbp}
                  , sub Op2{src = imm (16 :: Word64), dest = Rsp}
                  , -- { }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rax}
                  , -- { rax -> address(-8(%rbp)) }
                    mov Op2{src = imm (99 :: Word64), dest = Rbx}
                  , -- { rax -> address(-8(%rbp)), rbx -> 99 }
                    Inst2_im Mov Op2{src = imm (99 :: Word64), dest = Mem{base = BaseRegister Rbp, offset = -8}}
                  , -- { rax -> address(-8(%rbp)), rbx -> 99, (rax) -> 99 }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rbx}
                  , -- { rax -> address(-8(%rbp)), (rax) -> 99, rbx -> address(-16(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rcx}
                  , -- { rax -> address(-8(%rbp)), (rax) -> 99, rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)) }
                    mov Op2{src = imm (Symbol "type_Uint64"), dest = Rax}
                  , -- { rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rdx}
                  , -- { rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)), rdx -> address(-16(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rbx}
                  , -- { rbx -> address(-8(%rbp)), rcx -> address(-8(%rbp)), rdx -> address(-16(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rcx}
                  , -- { rbx -> address(-8(%rbp)), rcx -> address(-16(%rbp)), rdx -> address(-16(%rbp)) }
                    call (Symbol "id")
                  , -- { }
                    load Op2{src = Mem{base = BaseRegister Rax, offset = 0}, dest = Rax}
                  , add Op2{src = imm (1 :: Word64), dest = Rax}
                  ]
          propagateConstants_X86_64 input `shouldBe` output
      describe "deadCodeElimination" $ do
        it "1" $ do
          let input =
                fmap
                  Instruction
                  [ mov Op2{src = Rsp, dest = Rbp}
                  , sub Op2{src = imm (16 :: Word64), dest = Rsp}
                  , -- { }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rax}
                  , -- { rax -> address(-8(%rbp)) }
                    mov Op2{src = imm (99 :: Word64), dest = Rbx}
                  , -- { rax -> address(-8(%rbp)), rbx -> 99 }
                    Inst2_im Mov Op2{src = imm (99 :: Word64), dest = Mem{base = BaseRegister Rax, offset = 0}}
                  , -- { rax -> address(-8(%rbp)), rbx -> 99, (rax) -> 99 }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rbx}
                  , -- { rax -> address(-8(%rbp)), (rax) -> 99, rbx -> address(-16(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rcx}
                  , -- { rax -> address(-8(%rbp)), (rax) -> 99, rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)) }
                    mov Op2{src = imm (Symbol "type_Uint64"), dest = Rax}
                  , -- { rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rdx}
                  , -- { rbx -> address(-16(%rbp)), rcx -> address(-8(%rbp)), rdx -> address(-16(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rbx}
                  , -- { rbx -> address(-8(%rbp)), rcx -> address(-8(%rbp)), rdx -> address(-16(%rbp)) }
                    lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rcx}
                  , -- { rbx -> address(-8(%rbp)), rcx -> address(-16(%rbp)), rdx -> address(-16(%rbp)) }
                    call (Symbol "id")
                  , -- { }
                    load Op2{src = Mem{base = BaseRegister Rax, offset = 0}, dest = Rax}
                  , add Op2{src = imm (1 :: Word64), dest = Rax}
                  ]
          let output =
                fmap
                  Instruction
                  [ mov Op2{src = Rsp, dest = Rbp}
                  , sub Op2{src = imm (16 :: Word64), dest = Rsp}
                  , lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rax}
                  , Inst2_im Mov Op2{src = imm (99 :: Word64), dest = Mem{base = BaseRegister Rax, offset = 0}}
                  , mov Op2{src = imm (Symbol "type_Uint64"), dest = Rax}
                  , lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rdx}
                  , lea Op2{src = Mem{base = BaseRegister Rbp, offset = -8}, dest = Rbx}
                  , lea Op2{src = Mem{base = BaseRegister Rbp, offset = -16}, dest = Rcx}
                  , call (Symbol "id")
                  , load Op2{src = Mem{base = BaseRegister Rax, offset = 0}, dest = Rax}
                  , add Op2{src = imm (1 :: Word64), dest = Rax}
                  ]
          deadCodeElimination_X86_64 input `shouldBe` output