{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Metis.AllocateRegisters (
  allocateRegisters_X86_64,

  -- * Internals
  Location (..),
  AllocateRegistersState (..),
  initialAllocateRegistersState,
  allocateRegistersExpr_X86_64,
  allocateRegistersCompound_X86_64,
) where

import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (evalStateT)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Int (Int64)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Stack (HasCallStack)
import qualified Metis.Anf as Anf
import Metis.Isa (Add, Instruction, Isa, Memory (..), Register, Sub, add, imm, mov, pop, push, sub)
import Metis.Isa.X86_64 (Register (..), X86_64)
import qualified Metis.Literal as Literal
import Metis.Log (MonadLog)
import qualified Metis.Log as Log
import qualified Metis.Type as Type

data Location isa
  = Register (Register isa)
  | Stack {offset :: Int64}

deriving instance (Show (Register isa)) => Show (Location isa)

data AllocateRegistersState isa = AllocateRegistersState
  { nextStackOffset :: Int64
  , available :: Seq (Register isa)
  , locations :: HashMap Anf.Var (Location isa)
  }

initialAllocateRegistersState :: Seq (Register isa) -> AllocateRegistersState isa
initialAllocateRegistersState available =
  AllocateRegistersState
    { nextStackOffset = 0
    , available
    , locations = mempty
    }

allocateRegisters_X86_64 ::
  (MonadLog m) =>
  Seq (Register X86_64) ->
  Anf.Expr ->
  m ([Instruction X86_64], Location X86_64)
allocateRegisters_X86_64 available expr =
  evalStateT
    (allocateRegistersExpr_X86_64 mempty expr)
    (initialAllocateRegistersState available)

allocateRegistersExpr_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  HashMap Anf.Var Word64 ->
  Anf.Expr ->
  m ([Instruction X86_64], Location X86_64)
allocateRegistersExpr_X86_64 varSizes expr =
  case expr of
    Anf.Simple s ->
      case s of
        Anf.Var var -> do
          location <- autoAssignVar varSizes var
          pure ([], location)
        Anf.Literal lit -> do
          location <- allocLocation (Type.sizeOf $ Literal.typeOf lit)
          let insts = case location of
                Stack offset ->
                  [mov (imm lit) Mem{base = Rbp, offset}]
                Register register ->
                  [mov (imm lit) register]
          freeLocation location
          pure (insts, location)
    Anf.LetS var varInfo value rest -> do
      (rest', a) <- allocateRegistersExpr_X86_64 (HashMap.insert var varInfo.size varSizes) rest
      mLocation <- varLocation var
      case mLocation of
        Nothing ->
          pure (rest', a)
        Just location -> do
          modify (\s -> s{locations = HashMap.delete var s.locations})
          value' <- allocateRegistersSimple_X86_64 location value
          pure (value' <> rest', a)
    Anf.LetC var varInfo value rest -> do
      (rest', a) <- allocateRegistersExpr_X86_64 (HashMap.insert var varInfo.size varSizes) rest
      mLocation <- varLocation var
      case mLocation of
        Nothing ->
          pure (rest', a)
        Just location -> do
          modify (\s -> s{locations = HashMap.delete var s.locations})
          value' <- allocateRegistersCompound_X86_64 varSizes location value
          pure (value' <> rest', a)

allocateRegistersSimple_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m) =>
  Location X86_64 ->
  Anf.Simple ->
  m [Instruction X86_64]
allocateRegistersSimple_X86_64 destination simple =
  case simple of
    Anf.Var var ->
      [] <$ assignVar var destination
    Anf.Literal lit -> do
      let insts = case destination of
            Stack offset ->
              [mov (imm lit) Mem{base = Rbp, offset}]
            Register register ->
              [mov (imm lit) register]
      freeLocation destination
      pure insts

allocateRegistersCompound_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  HashMap Anf.Var Word64 ->
  Location X86_64 ->
  Anf.Compound ->
  m [Instruction X86_64]
allocateRegistersCompound_X86_64 varSizes destination compound = do
  case compound of
    Anf.Binop op a b -> do
      Log.trace . Text.pack $ show (destination, a, b)

      available <- gets (.available)
      Log.trace . Text.pack $ "available registers: " <> show available

      let
        op' :: (Add X86_64 a b, Sub X86_64 a b) => a -> b -> Instruction X86_64
        op' =
          case op of
            Anf.Add -> add
            Anf.Subtract -> sub

      case (destination, a, b) of
        (Stack offset, Anf.Literal litA, Anf.Literal litB) -> do
          let destination' = Mem{base = Rbp, offset}
          pure [mov (imm litB) destination', op' (imm litA) destination']
        (Stack offset, Anf.Var varA, Anf.Literal litB) -> do
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
        (Stack offset, Anf.Literal litA, Anf.Var varB) -> do
          let destination' = Mem{base = Rbp, offset}
          assignVar varB destination
          pure [op' (imm litA) destination']
        (Stack offset, Anf.Var varA, Anf.Var varB) -> do
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
        (Register destination', Anf.Literal litA, Anf.Literal litB) ->
          pure [mov (imm litB) destination', op' (imm litA) destination']
        (Register destination', Anf.Var varA, Anf.Literal litB) -> do
          locationA <- autoAssignVar varSizes varA
          case locationA of
            Stack offset' -> do
              let locationA' = Mem{base = Rbp, offset = offset'}
              pure [mov (imm litB) destination', op' locationA' destination']
            Register locationA' ->
              pure [mov (imm litB) destination', op' locationA' destination']
        (Register destination', Anf.Literal litA, Anf.Var varB) -> do
          assignVar varB destination
          pure [op' (imm litA) destination']
        (Register destination', Anf.Var varA, Anf.Var varB) -> do
          assignVar varB destination
          locationA <- autoAssignVar varSizes varA
          case locationA of
            Stack offset -> do
              let locationA' = Mem{base = Rbp, offset}
              pure [op' locationA' destination']
            Register locationA' ->
              pure [op' locationA' destination']

assignVar ::
  forall isa m.
  (HasCallStack) =>
  (MonadState (AllocateRegistersState isa) m, Isa isa) =>
  Anf.Var ->
  Location isa ->
  m ()
assignVar var location =
  modify (\s -> (s :: AllocateRegistersState isa){locations = HashMap.insert var location s.locations})

allocLocation ::
  (MonadState (AllocateRegistersState isa) m) =>
  Word64 ->
  m (Location isa)
allocLocation size = do
  available <- gets (.available)
  case Seq.viewl available of
    Seq.EmptyL -> do
      offset <- gets (.nextStackOffset)
      let location = Stack offset
      modify (\s -> s{nextStackOffset = offset - fromIntegral @Word64 @Int64 size})
      pure location
    register Seq.:< available' -> do
      modify (\s -> s{available = available'})
      pure $ Register register

freeLocation ::
  (MonadState (AllocateRegistersState isa) m) =>
  Location isa ->
  m ()
freeLocation location =
  case location of
    Stack{} -> pure ()
    Register register ->
      modify (\s -> s{available = s.available Seq.|> register})

autoAssignVar ::
  (HasCallStack) =>
  (MonadState (AllocateRegistersState isa) m, Isa isa) =>
  HashMap Anf.Var Word64 ->
  Anf.Var ->
  m (Location isa)
autoAssignVar varSizes var = do
  mLocation <- gets (HashMap.lookup var . (.locations))
  case mLocation of
    Nothing -> do
      location <- allocLocation (Maybe.fromMaybe (error $ show var <> " missing from varSizes") $ HashMap.lookup var varSizes)
      assignVar var location
      pure location
    Just location ->
      pure location

varLocation ::
  (MonadState (AllocateRegistersState isa) m) =>
  Anf.Var ->
  m (Maybe (Location isa))
varLocation var = gets (HashMap.lookup var . (.locations))
