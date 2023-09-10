module Test.RegisterAllocation (spec) where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalState)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Sequence as Seq
import Metis.RegisterAllocation (
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  AnyVirtual (..),
  Imm (..),
  Inst (..),
  Mem (..),
  Physical (..),
  Reg (..),
  Virtual (..),
  allocRegisters,
  allocRegistersInst,
 )
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.RegisterAllocation" $ do
    it "1" $ do
      let input =
            [ Mov_ri (Virtual 0) (Word64 1)
            , Mov_ri (Virtual 1) (Word64 2)
            , Add_rr (Virtual 2) (Virtual 0) (Virtual 1)
            , Mov_ri (Virtual 3) (Word64 3)
            , Mov_ri (Virtual 4) (Word64 4)
            , Add_rr (Virtual 5) (Virtual 3) (Virtual 4)
            , Add_rr (Virtual 6) (Virtual 2) (Virtual 5)
            ]
      let
        result =
          flip
            evalState
            AllocRegistersState
              { locations = const Nothing
              , varSizes = mempty
              , freeRegisters = Seq.fromList [Rax, Rbx, Rcx, Rdx]
              , occupiedRegisters = mempty
              , freeMemory = mempty
              , stackFrameTop = 0
              }
            . flip
              runReaderT
              AllocRegistersEnv
                { kills =
                    HashMap.fromList
                      [ (AnyVirtual (Virtual 0), mempty)
                      , (AnyVirtual (Virtual 1), mempty)
                      , (AnyVirtual (Virtual 2), HashSet.fromList [AnyVirtual (Virtual 0), AnyVirtual (Virtual 1)])
                      , (AnyVirtual (Virtual 3), mempty)
                      , (AnyVirtual (Virtual 4), mempty)
                      , (AnyVirtual (Virtual 5), HashSet.fromList [AnyVirtual (Virtual 3), AnyVirtual (Virtual 4)])
                      , (AnyVirtual (Virtual 6), HashSet.fromList [AnyVirtual (Virtual 2), AnyVirtual (Virtual 5)])
                      ]
                }
            $ allocRegisters allocRegistersInst input
      result
        `shouldBe` [ Mov_ri (Register Rax) (Word64 1)
                   , Mov_ri (Register Rbx) (Word64 2)
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   , Mov_ri (Register Rbx) (Word64 3)
                   , Mov_ri (Register Rcx) (Word64 4)
                   , Add_rr (Register Rbx) (Register Rbx) (Register Rcx)
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   ]

    it "2" $ do
      let input =
            [ Mov_ri (Virtual 0) (Word64 1)
            , Mov_ri (Virtual 1) (Word64 2)
            , Add_rr (Virtual 2) (Virtual 0) (Virtual 1)
            , Mov_ri (Virtual 3) (Word64 3)
            , Mov_ri (Virtual 4) (Word64 4)
            , Add_rr (Virtual 5) (Virtual 3) (Virtual 4)
            , Add_rr (Virtual 6) (Virtual 2) (Virtual 5)
            ]
      let
        result =
          flip
            evalState
            AllocRegistersState
              { locations = const Nothing
              , varSizes = mempty
              , freeRegisters = Seq.fromList [Rax, Rbx]
              , occupiedRegisters = mempty
              , freeMemory = mempty
              , stackFrameTop = 0
              }
            . flip
              runReaderT
              AllocRegistersEnv
                { kills =
                    HashMap.fromList
                      [ (AnyVirtual (Virtual 0), mempty)
                      , (AnyVirtual (Virtual 1), mempty)
                      , (AnyVirtual (Virtual 2), HashSet.fromList [AnyVirtual (Virtual 0), AnyVirtual (Virtual 1)])
                      , (AnyVirtual (Virtual 3), mempty)
                      , (AnyVirtual (Virtual 4), mempty)
                      , (AnyVirtual (Virtual 5), HashSet.fromList [AnyVirtual (Virtual 3), AnyVirtual (Virtual 4)])
                      , (AnyVirtual (Virtual 6), HashSet.fromList [AnyVirtual (Virtual 2), AnyVirtual (Virtual 5)])
                      ]
                }
            $ allocRegisters allocRegistersInst input
      result
        `shouldBe` [ Mov_ri (Register Rax) (Word64 1)
                   , Mov_ri (Register Rbx) (Word64 2)
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   , Mov_ri (Register Rbx) (Word64 3)
                   , Mov_mr (Memory Mem{base = Rbp, offset = -8, size = 8}) (Register Rax)
                   , Mov_ri (Register Rax) (Word64 4)
                   , Add_rr (Register Rbx) (Register Rbx) (Register Rax)
                   , Mov_rm (Register Rax) (Memory Mem{base = Rbp, offset = -8, size = 8})
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   ]