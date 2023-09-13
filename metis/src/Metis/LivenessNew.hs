{-# LANGUAGE OverloadedRecordDot #-}

module Metis.LivenessNew (
  livenessBlocks,
  livenessBlock,
  livenessInstructions,
  livenessInstruction,
  livenessTerminator,
) where

import Data.Buildable (collectL')
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Metis.SSA (Block (..), Compound (..), Instruction (..), Simple (..), Terminator (..))
import Metis.SSA.Var (Var)
import Metis.Type (Type)

livenessInstruction ::
  HashSet Var ->
  Instruction ->
  (HashSet Var, HashMap Var (HashSet Var))
livenessInstruction usedAfter inst =
  case inst of
    LetS var _ value ->
      let valueVars = varsSimple value
          usedBefore = HashSet.delete var usedAfter <> valueVars
       in (usedBefore, HashMap.singleton var (valueVars `HashSet.difference` usedAfter))
    LetC var _ value ->
      let valueVars = varsCompound value
          usedBefore = HashSet.delete var usedAfter <> valueVars
       in (usedBefore, HashMap.singleton var (valueVars `HashSet.difference` usedAfter))

livenessTerminator ::
  Terminator ->
  HashSet Var
livenessTerminator term =
  case term of
    Return value ->
      varsSimple value
    IfThenElse cond _a _b ->
      varsSimple cond
    Jump _label arg ->
      varsSimple arg

livenessInstructions ::
  HashSet Var ->
  [Instruction] ->
  (HashSet Var, HashMap Var (HashSet Var))
livenessInstructions usedAfter insts =
  case insts of
    [] ->
      (usedAfter, mempty)
    inst : insts' ->
      let
        (usedBefore, kills) = livenessInstructions usedAfter insts'
        (usedBefore', kills') = livenessInstruction usedBefore inst
       in
        (usedBefore', kills <> kills')

livenessBlock ::
  Block ->
  HashMap Var (HashSet Var)
livenessBlock block =
  let
    usedBefore = livenessTerminator block.terminator
    (_usedBefore', kills) = livenessInstructions usedBefore block.instructions
   in
    kills

livenessBlocks :: [Block] -> HashMap Var (HashSet Var)
livenessBlocks = foldMap livenessBlock

varsType :: Type Var -> HashSet Var
varsType = collectL'

varsCompound :: Compound -> HashSet Var
varsCompound compound =
  case compound of
    Binop _ a b -> varsSimple a <> varsSimple b
    Call a bs -> varsSimple a <> collectL' bs
    Alloca ty -> varsType ty
    Store a b -> varsSimple a <> varsSimple b
    Load a -> varsSimple a
    GetTypeDictField a _field -> varsSimple a

varsSimple :: Simple -> HashSet Var
varsSimple simple =
  case simple of
    Var var -> HashSet.singleton var
    Name{} -> mempty
    Literal{} -> mempty
    Type{} -> mempty