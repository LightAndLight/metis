{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.RegisterAllocation (spec) where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalState)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import qualified Data.Sequence as Seq
import GHC.Generics (Generic)
import Metis.InstSelectionNew (Var (..))
import Metis.IsaNew (
  Address (..),
  AddressBase (..),
  Immediate (..),
  Isa (..),
  generalPurposeRegisters,
 )
import Metis.LivenessNew (Liveness (..))
import Metis.RegisterAllocation (
  AllocRegisters (..),
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Usage (..),
  VarInfo (..),
  allocRegisters,
 )
import qualified Metis.SSA.Var as SSA
import Test.Hspec (Spec, describe, it, shouldBe)

data MockIsa

instance Isa MockIsa where
  pointerSize = 8

  data Register MockIsa = Rax | Rbx | Rcx | Rdx | Rbp
    deriving (Eq, Show, Generic)

  registerSize _ = 8

  registerName Rax = "rax"
  registerName Rbx = "rbx"
  registerName Rcx = "rcx"
  registerName Rdx = "rdx"
  registerName Rbp = "rbp"

  generalPurposeRegisters = Seq.fromList [Rax, Rbx, Rcx, Rdx]

  framePointerRegister = Rbp

  data Instruction MockIsa var
    = Mov_ri var Immediate
    | Mov_rm var (Address var)
    | Mov_mi (Address var) Immediate
    | Mov_mr (Address var) var
    | Add_ri var var Immediate
    | Add_rr var var var
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance Hashable (Register MockIsa)

allocRegistersMockIsa :: AllocRegisters MockIsa
allocRegistersMockIsa =
  AllocRegisters
    { instructionVarInfo
    , load = Mov_rm
    , store = Mov_mr
    }
  where
    instructionVarInfo ::
      Instruction MockIsa var ->
      Instruction MockIsa (VarInfo var)
    instructionVarInfo inst =
      case inst of
        Mov_ri dest imm ->
          Mov_ri
            (VarInfo DefNew dest)
            imm
        Mov_rm dest src ->
          Mov_rm
            (VarInfo DefNew dest)
            (fmap (VarInfo (Use [])) src)
        Mov_mi dest imm ->
          Mov_mi
            (fmap (VarInfo (Use [])) dest)
            imm
        Mov_mr dest src ->
          Mov_mr
            (fmap (VarInfo (Use [])) dest)
            (VarInfo (Use []) src)
        Add_ri dest src imm ->
          Add_ri
            (VarInfo (DefReuse src) dest)
            (VarInfo (Use []) src)
            imm
        Add_rr dest src1 src2 ->
          Add_rr
            (VarInfo (DefReuse src1) dest)
            (VarInfo (Use [src2]) src1)
            (VarInfo (Use [src1]) src2)

spec :: Spec
spec =
  describe "Test.RegisterAllocation" $ do
    it "1" $ do
      let input =
            [ Mov_ri (Virtual $ SSA.unsafeVar 0) (Word64 1)
            , Mov_ri (Virtual $ SSA.unsafeVar 1) (Word64 2)
            , Add_rr (Virtual $ SSA.unsafeVar 2) (Virtual $ SSA.unsafeVar 0) (Virtual $ SSA.unsafeVar 1)
            , Mov_ri (Virtual $ SSA.unsafeVar 3) (Word64 3)
            , Mov_ri (Virtual $ SSA.unsafeVar 4) (Word64 4)
            , Add_rr (Virtual $ SSA.unsafeVar 5) (Virtual $ SSA.unsafeVar 3) (Virtual $ SSA.unsafeVar 4)
            , Add_rr (Virtual $ SSA.unsafeVar 6) (Virtual $ SSA.unsafeVar 2) (Virtual $ SSA.unsafeVar 5)
            ]
      let
        result =
          flip
            evalState
            AllocRegistersState
              { locations = mempty
              , varSizes = mempty
              , freeRegisters = generalPurposeRegisters @MockIsa
              , occupiedRegisters = mempty
              , freeMemory = mempty
              , stackFrameTop = 0
              }
            . flip
              runReaderT
              AllocRegistersEnv
                { liveness =
                    Liveness
                      { varKills =
                          HashMap.fromList
                            [ (SSA.unsafeVar 0, mempty)
                            , (SSA.unsafeVar 1, mempty)
                            , (SSA.unsafeVar 2, HashSet.fromList [SSA.unsafeVar 0, SSA.unsafeVar 1])
                            , (SSA.unsafeVar 3, mempty)
                            , (SSA.unsafeVar 4, mempty)
                            , (SSA.unsafeVar 5, HashSet.fromList [SSA.unsafeVar 3, SSA.unsafeVar 4])
                            , (SSA.unsafeVar 6, HashSet.fromList [SSA.unsafeVar 2, SSA.unsafeVar 5])
                            ]
                      , labelKills = mempty
                      }
                }
            $ allocRegisters allocRegistersMockIsa input
      result
        `shouldBe` [ Mov_ri Rax (Word64 1)
                   , Mov_ri Rbx (Word64 2)
                   , Add_rr Rax Rax Rbx
                   , Mov_ri Rbx (Word64 3)
                   , Mov_ri Rcx (Word64 4)
                   , Add_rr Rbx Rbx Rcx
                   , Add_rr Rax Rax Rbx
                   ]

    it "2" $ do
      let input =
            [ Mov_ri (Virtual $ SSA.unsafeVar 0) (Word64 1)
            , Mov_ri (Virtual $ SSA.unsafeVar 1) (Word64 2)
            , Add_rr (Virtual $ SSA.unsafeVar 2) (Virtual $ SSA.unsafeVar 0) (Virtual $ SSA.unsafeVar 1)
            , Mov_ri (Virtual $ SSA.unsafeVar 3) (Word64 3)
            , Mov_ri (Virtual $ SSA.unsafeVar 4) (Word64 4)
            , Add_rr (Virtual $ SSA.unsafeVar 5) (Virtual $ SSA.unsafeVar 3) (Virtual $ SSA.unsafeVar 4)
            , Add_rr (Virtual $ SSA.unsafeVar 6) (Virtual $ SSA.unsafeVar 2) (Virtual $ SSA.unsafeVar 5)
            ]
      let
        result =
          flip
            evalState
            AllocRegistersState
              { locations = mempty
              , varSizes = mempty
              , freeRegisters = Seq.fromList [Rax, Rbx]
              , occupiedRegisters = mempty
              , freeMemory = mempty
              , stackFrameTop = 0
              }
            . flip
              runReaderT
              AllocRegistersEnv
                { liveness =
                    Liveness
                      { varKills =
                          HashMap.fromList
                            [ (SSA.unsafeVar 0, mempty)
                            , (SSA.unsafeVar 1, mempty)
                            , (SSA.unsafeVar 2, HashSet.fromList [SSA.unsafeVar 0, SSA.unsafeVar 1])
                            , (SSA.unsafeVar 3, mempty)
                            , (SSA.unsafeVar 4, mempty)
                            , (SSA.unsafeVar 5, HashSet.fromList [SSA.unsafeVar 3, SSA.unsafeVar 4])
                            , (SSA.unsafeVar 6, HashSet.fromList [SSA.unsafeVar 2, SSA.unsafeVar 5])
                            ]
                      , labelKills = mempty
                      }
                }
            $ allocRegisters allocRegistersMockIsa input
      result
        `shouldBe` [ Mov_ri Rax (Word64 1)
                   , Mov_ri Rbx (Word64 2)
                   , Add_rr Rax Rax Rbx
                   , Mov_ri Rbx (Word64 3)
                   , Mov_mr Address{base = BaseVar Rbp, offset = -8} Rax
                   , Mov_ri Rax (Word64 4)
                   , Add_rr Rbx Rbx Rax
                   , Mov_rm Rax Address{base = BaseVar Rbp, offset = -8}
                   , Add_rr Rax Rax Rbx
                   ]