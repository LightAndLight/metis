{-# LANGUAGE TypeApplications #-}

module Test.RegisterAllocation (spec) where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalState)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Sequence as Seq
import Metis.IsaNew (Immediate (..), Memory (..), MemoryBase (..), generalPurposeRegisters)
import Metis.RegisterAllocation (
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Instruction (..),
  MockIsa,
  Physical (..),
  Register (..),
  allocRegisters,
  allocRegistersMockIsa,
 )
import qualified Metis.SSA.Var as SSA
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "Test.RegisterAllocation" $ do
    it "1" $ do
      let input =
            [ Mov_ri (SSA.unsafeVar 0) (Word64 1)
            , Mov_ri (SSA.unsafeVar 1) (Word64 2)
            , Add_rr (SSA.unsafeVar 2) (SSA.unsafeVar 0) (SSA.unsafeVar 1)
            , Mov_ri (SSA.unsafeVar 3) (Word64 3)
            , Mov_ri (SSA.unsafeVar 4) (Word64 4)
            , Add_rr (SSA.unsafeVar 5) (SSA.unsafeVar 3) (SSA.unsafeVar 4)
            , Add_rr (SSA.unsafeVar 6) (SSA.unsafeVar 2) (SSA.unsafeVar 5)
            ]
      let
        result =
          flip
            evalState
            AllocRegistersState
              { locations = const Nothing
              , varSizes = mempty
              , freeRegisters = generalPurposeRegisters @MockIsa
              , occupiedRegisters = mempty
              , freeMemory = mempty
              , stackFrameTop = 0
              }
            . flip
              runReaderT
              AllocRegistersEnv
                { kills =
                    HashMap.fromList
                      [ (SSA.AnyVar (SSA.unsafeVar 0), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 1), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 2), HashSet.fromList [SSA.AnyVar (SSA.unsafeVar 0), SSA.AnyVar (SSA.unsafeVar 1)])
                      , (SSA.AnyVar (SSA.unsafeVar 3), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 4), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 5), HashSet.fromList [SSA.AnyVar (SSA.unsafeVar 3), SSA.AnyVar (SSA.unsafeVar 4)])
                      , (SSA.AnyVar (SSA.unsafeVar 6), HashSet.fromList [SSA.AnyVar (SSA.unsafeVar 2), SSA.AnyVar (SSA.unsafeVar 5)])
                      ]
                }
            $ allocRegisters allocRegistersMockIsa input
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
            [ Mov_ri (SSA.unsafeVar 0) (Word64 1)
            , Mov_ri (SSA.unsafeVar 1) (Word64 2)
            , Add_rr (SSA.unsafeVar 2) (SSA.unsafeVar 0) (SSA.unsafeVar 1)
            , Mov_ri (SSA.unsafeVar 3) (Word64 3)
            , Mov_ri (SSA.unsafeVar 4) (Word64 4)
            , Add_rr (SSA.unsafeVar 5) (SSA.unsafeVar 3) (SSA.unsafeVar 4)
            , Add_rr (SSA.unsafeVar 6) (SSA.unsafeVar 2) (SSA.unsafeVar 5)
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
                      [ (SSA.AnyVar (SSA.unsafeVar 0), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 1), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 2), HashSet.fromList [SSA.AnyVar (SSA.unsafeVar 0), SSA.AnyVar (SSA.unsafeVar 1)])
                      , (SSA.AnyVar (SSA.unsafeVar 3), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 4), mempty)
                      , (SSA.AnyVar (SSA.unsafeVar 5), HashSet.fromList [SSA.AnyVar (SSA.unsafeVar 3), SSA.AnyVar (SSA.unsafeVar 4)])
                      , (SSA.AnyVar (SSA.unsafeVar 6), HashSet.fromList [SSA.AnyVar (SSA.unsafeVar 2), SSA.AnyVar (SSA.unsafeVar 5)])
                      ]
                }
            $ allocRegisters allocRegistersMockIsa input
      result
        `shouldBe` [ Mov_ri (Register Rax) (Word64 1)
                   , Mov_ri (Register Rbx) (Word64 2)
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   , Mov_ri (Register Rbx) (Word64 3)
                   , Mov_mr (Memory Mem{base = BaseRegister Rbp, offset = -8} 8) (Register Rax)
                   , Mov_ri (Register Rax) (Word64 4)
                   , Add_rr (Register Rbx) (Register Rbx) (Register Rax)
                   , Mov_rm (Register Rax) (Memory Mem{base = BaseRegister Rbp, offset = -8} 8)
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   ]