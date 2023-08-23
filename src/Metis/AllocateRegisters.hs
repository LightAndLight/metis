{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Metis.AllocateRegisters (
  Expr2 (..),
  Expr3 (..),
  Compound (..),
  Simple (..),
  Location (..),
  AllocateRegistersState (..),
  initialAllocateRegistersState,
  allocateRegisters_X86_64,
  allocateRegistersExpr_X86_64,
  allocateRegistersCompound_X86_64,
  allocateRegistersSimple,
) where

import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (evalState)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Int (Int64)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Word (Word64)
import Metis.Isa (Add, Instruction, Isa, Memory (..), Register, Sub, add, imm, mov, pop, push, sub)
import Metis.Isa.X86_64 (Register (..), X86_64)
import Metis.Literal (Literal)
import qualified Metis.SSA as SSA

data Location isa
  = Register (Register isa)
  | Stack {offset :: Int64}

data Simple isa
  = Location (Location isa)
  | Literal Literal

data Compound isa
  = Add (Simple isa) (Simple isa)
  | Subtract (Simple isa) (Simple isa)

data Expr2 isa
  = Var2 (Location isa)
  | Inst2 (Compound isa) (Expr2 isa)

data Expr3 isa
  = Var3 (Location isa)
  | Let3 (Location isa) (Compound isa) (Expr3 isa)

data AllocateRegistersState isa = AllocateRegistersState
  { nextStackOffset :: Int64
  , available :: Seq (Register isa)
  , locations :: HashMap SSA.Var (Location isa)
  }

initialAllocateRegistersState :: Seq (Register isa) -> AllocateRegistersState isa
initialAllocateRegistersState available =
  AllocateRegistersState
    { nextStackOffset = 0
    , available
    , locations = mempty
    }

allocateRegisters_X86_64 ::
  Seq (Register X86_64) ->
  SSA.Expr ->
  ([Instruction X86_64], Location X86_64)
allocateRegisters_X86_64 available expr =
  evalState
    (allocateRegistersExpr_X86_64 mempty expr)
    (initialAllocateRegistersState available)

allocateRegistersExpr_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m) =>
  HashMap SSA.Var Word64 ->
  SSA.Expr ->
  m ([Instruction X86_64], Location X86_64)
allocateRegistersExpr_X86_64 varSizes expr =
  case expr of
    SSA.Var var -> do
      location <- autoAssignVar varSizes var
      pure ([], location)
    SSA.Let var varInfo value rest -> do
      (rest', a) <- allocateRegistersExpr_X86_64 (HashMap.insert var varInfo.size varSizes) rest
      varUsage <- unassignVar var
      case varUsage of
        Unused ->
          pure (rest', a)
        Used location -> do
          value' <- allocateRegistersCompound_X86_64 varSizes location value
          pure (value' <> rest', a)

allocateRegistersCompound_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m) =>
  HashMap SSA.Var Word64 ->
  Location X86_64 ->
  SSA.Compound ->
  m [Instruction X86_64]
allocateRegistersCompound_X86_64 varSizes destination compound =
  case compound of
    SSA.Simple s ->
      case s of
        SSA.SVar var -> do
          assignVar var destination
          pure []
        SSA.Literal lit ->
          case destination of
            Stack offset ->
              pure [mov (imm lit) Mem{base = Rbp, offset}]
            Register register ->
              pure [mov (imm lit) register]
    SSA.Binop op a b -> do
      let
        op' :: (Add X86_64 a b, Sub X86_64 a b) => a -> b -> Instruction X86_64
        op' =
          case op of
            SSA.Add -> add
            SSA.Subtract -> sub
      case (destination, a, b) of
        (Stack offset, SSA.Literal litA, SSA.Literal litB) -> do
          let destination' = Mem{base = Rbp, offset}
          pure [mov (imm litB) destination', op' (imm litA) destination']
        (Register destination', SSA.Literal litA, SSA.Literal litB) ->
          pure [mov (imm litB) destination', op' (imm litA) destination']
        (Stack offset, SSA.SVar varA, SSA.Literal litB) -> do
          let destination' = Mem{base = Rbp, offset}
          locationA <- autoAssignVar varSizes varA
          case locationA of
            Stack offsetA -> do
              pure
                [ mov (imm litB) destination'
                , push Rax
                , mov Mem{base = Rbp, offset = offsetA} Rax
                , op' Rax destination'
                , pop Rax
                ]
            Register registerA ->
              pure [mov (imm litB) destination', op' registerA destination']
        (Register destination', SSA.SVar varA, SSA.Literal litB) -> do
          locationA <- autoAssignVar varSizes varA
          case locationA of
            Stack offset' -> do
              let locationA' = Mem{base = Rbp, offset = offset'}
              pure [mov (imm litB) destination', op' locationA' destination']
            Register locationA' ->
              pure [mov (imm litB) destination', op' locationA' destination']
        (Stack offset, SSA.Literal litA, SSA.SVar varB) -> do
          let destination' = Mem{base = Rbp, offset}
          assignVar varB destination
          pure [op' (imm litA) destination']
        (Register destination', SSA.Literal litA, SSA.SVar varB) -> do
          assignVar varB destination
          pure [op' (imm litA) destination']
        (Stack offset, SSA.SVar varA, SSA.SVar varB) -> do
          let destination' = Mem{base = Rbp, offset}
          assignVar varB destination
          locationA <- autoAssignVar varSizes varA
          case locationA of
            Stack offsetA ->
              pure
                [ push Rax
                , mov Mem{base = Rbp, offset = offsetA} Rax
                , op' Rax destination'
                , pop Rax
                ]
            Register registerA ->
              pure [op' registerA destination']
        (Register destination', SSA.SVar varA, SSA.SVar varB) -> do
          assignVar varB destination
          locationA <- autoAssignVar varSizes varA
          case locationA of
            Stack offset -> do
              let locationA' = Mem{base = Rbp, offset}
              pure [op' locationA' destination']
            Register locationA' ->
              pure [op' locationA' destination']

allocateRegistersSimple ::
  (MonadState (AllocateRegistersState isa) m, Isa isa) =>
  HashMap SSA.Var Word64 ->
  SSA.Simple ->
  m (Simple isa)
allocateRegistersSimple varSizes simple =
  case simple of
    SSA.SVar var -> Location <$> autoAssignVar varSizes var
    SSA.Literal lit -> pure $ Literal lit

assignVar ::
  forall isa m.
  (MonadState (AllocateRegistersState isa) m, Isa isa) =>
  SSA.Var ->
  Location isa ->
  m ()
assignVar var location =
  modify
    ( \s ->
        (s :: AllocateRegistersState isa)
          { available =
              case location of
                Register register ->
                  maybe
                    (error $ "attempting to assign unavailable register " <> show register)
                    (`Seq.deleteAt` s.available)
                    (Seq.findIndexL (== register) s.available)
                _ -> s.available
          , locations = HashMap.insert var location s.locations
          }
    )

autoAssignVar ::
  (MonadState (AllocateRegistersState isa) m, Isa isa) =>
  HashMap SSA.Var Word64 ->
  SSA.Var ->
  m (Location isa)
autoAssignVar varSizes var = do
  mLocation <- gets (HashMap.lookup var . (.locations))
  case mLocation of
    Nothing -> do
      available <- gets (.available)
      case Seq.viewl available of
        Seq.EmptyL -> do
          offset <- gets (.nextStackOffset)
          let size = Maybe.fromMaybe (error $ show var <> " missing from varSizes") $ HashMap.lookup var varSizes
          let location = Stack offset
          modify
            ( \s ->
                s
                  { nextStackOffset = offset - fromIntegral @Word64 @Int64 size
                  , locations = HashMap.insert var location s.locations
                  }
            )
          pure location
        register Seq.:< available' -> do
          let location = Register register
          assignVar var location
          modify (\s -> s{available = available'})
          pure location
    Just location ->
      pure location

data VarUsage isa
  = Used (Location isa)
  | Unused

unassignVar ::
  (MonadState (AllocateRegistersState isa) m) =>
  SSA.Var ->
  m (VarUsage isa)
unassignVar var = do
  mLocation <- gets (HashMap.lookup var . (.locations))
  case mLocation of
    Nothing -> pure Unused
    Just location -> do
      case location of
        Stack{} -> pure ()
        Register register ->
          modify (\s -> s{available = s.available Seq.|> register})
      pure $ Used location