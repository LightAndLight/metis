{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Test.RegisterAllocation (spec) where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalState)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import qualified Data.Sequence as Seq
import Data.Word (Word64)
import GHC.Generics (Generic)
import Metis.IsaNew (
  Address (..),
  AddressBase (..),
  Immediate (..),
  Isa (..),
  generalPurposeRegisters,
  mapVarsAddress,
  traverseVarsAddress,
 )
import Metis.RegisterAllocation (
  AllocRegisters (..),
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Physical (..),
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
    = Mov_ri (var (Register MockIsa)) Immediate
    | Mov_rm (var (Register MockIsa)) (Address MockIsa var)
    | Mov_mi (Address MockIsa var) Immediate
    | Mov_mr (Address MockIsa var) (var (Register MockIsa))
    | Add_ri (var (Register MockIsa)) (var (Register MockIsa)) Immediate
    | Add_rr (var (Register MockIsa)) (var (Register MockIsa)) (var (Register MockIsa))

instance Hashable (Register MockIsa)
deriving instance (forall a. (Show a) => Show (var a)) => Show (Instruction MockIsa var)
deriving instance (forall a. (Eq a) => Eq (var a)) => Eq (Instruction MockIsa var)

allocRegistersMockIsa :: AllocRegisters MockIsa
allocRegistersMockIsa =
  AllocRegisters
    { traverseVars
    , instructionVarInfo
    , load = Mov_rm
    , store = Mov_mr
    }
  where
    traverseVars ::
      (Applicative m) =>
      (forall a. (a ~ Register MockIsa) => var a -> m (var' a)) ->
      Instruction MockIsa var ->
      m (Instruction MockIsa var')
    traverseVars f inst =
      case inst of
        Mov_ri dest imm ->
          (\dest' -> Mov_ri dest' imm) <$> f dest
        Mov_rm dest src ->
          (\src' dest' -> Mov_rm dest' src') <$> traverseVarsAddress f src <*> f dest
        Mov_mi dest imm -> do
          (\dest' -> Mov_mi dest' imm) <$> traverseVarsAddress f dest
        Mov_mr dest src -> do
          (\src' dest' -> Mov_mr dest' src') <$> f src <*> traverseVarsAddress f dest
        Add_ri dest src imm -> do
          (\src' dest' -> Add_ri dest' src' imm) <$> f src <*> f dest
        Add_rr dest src1 src2 -> do
          (\src1' src2' dest' -> Add_rr dest' src1' src2') <$> f src1 <*> f src2 <*> f dest

    instructionVarInfo ::
      (forall a. var a -> Word64) ->
      Instruction MockIsa var ->
      Instruction MockIsa (VarInfo MockIsa var)
    instructionVarInfo _varSize inst =
      case inst of
        Mov_ri dest imm ->
          Mov_ri
            (VarInfo DefNew dest)
            imm
        Mov_rm dest src ->
          Mov_rm
            (VarInfo DefNew dest)
            (mapVarsAddress (VarInfo (Use [])) src)
        Mov_mi dest imm ->
          Mov_mi
            (mapVarsAddress (VarInfo (Use [])) dest)
            imm
        Mov_mr dest src ->
          Mov_mr
            (mapVarsAddress (VarInfo (Use [])) dest)
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
                   , Mov_mr Address{base = BaseVar $ Register Rbp, offset = -8} (Register Rax)
                   , Mov_ri (Register Rax) (Word64 4)
                   , Add_rr (Register Rbx) (Register Rbx) (Register Rax)
                   , Mov_rm (Register Rax) Address{base = BaseVar $ Register Rbp, offset = -8}
                   , Add_rr (Register Rax) (Register Rax) (Register Rbx)
                   ]