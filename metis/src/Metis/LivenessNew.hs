{-# LANGUAGE OverloadedRecordDot #-}

module Metis.LivenessNew (
  Liveness (..),
  livenessBlocks,
  livenessBlock,
  livenessInstructions,
  livenessInstruction,
  livenessTerminator,
) where

import Data.Buildable (collectL')
import Data.Foldable (fold)
import qualified Data.HashMap.Lazy as HashMap.Lazy
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Metis.SSA (
  Block (..),
  Compound (..),
  Instruction (..),
  Label (..),
  Simple (..),
  Terminator (..),
 )
import Metis.SSA.Var (Var)
import Metis.Type (Type)

data Liveness = Liveness
  { varKills :: HashMap Var (HashSet Var)
  , labelKills :: HashMap Label (HashSet Var)
  }
  deriving (Eq, Show)

instance Semigroup Liveness where
  a <> b =
    Liveness
      { varKills = a.varKills <> b.varKills
      , labelKills = HashMap.unionWith (<>) a.labelKills b.labelKills
      }

instance Monoid Liveness where
  mempty = Liveness{varKills = mempty, labelKills = mempty}

livenessInstruction ::
  HashSet Var ->
  Instruction ->
  (HashSet Var, Liveness)
livenessInstruction usedAfter inst =
  case inst of
    LetS var _ value ->
      let valueVars = varsSimple value
          usedBefore = HashSet.delete var usedAfter <> valueVars
       in ( usedBefore
          , Liveness
              { varKills = HashMap.singleton var (valueVars `HashSet.difference` usedAfter)
              , labelKills = mempty
              }
          )
    LetC var _ value ->
      let valueVars = varsCompound value
          usedBefore = HashSet.delete var usedAfter <> valueVars
       in ( usedBefore
          , Liveness
              { varKills = HashMap.singleton var (valueVars `HashSet.difference` usedAfter)
              , labelKills = mempty
              }
          )

livenessTerminator ::
  HashMap Label (HashSet Var) ->
  Terminator ->
  (HashSet Var, Liveness)
livenessTerminator labelUsedAfter term =
  case term of
    Return value ->
      let usedBefore = varsSimple value
       in (usedBefore, mempty)
    IfThenElse cond a b ->
      let vars = varsSimple cond
          aUsedAfter = fold $ HashMap.lookup a labelUsedAfter
          bUsedAfter = fold $ HashMap.lookup b labelUsedAfter
          abUsedAfter = aUsedAfter <> bUsedAfter
          usedBefore = abUsedAfter <> vars
          labelKills = vars `HashSet.difference` abUsedAfter
       in (usedBefore, mempty{labelKills = HashMap.fromList [(a, labelKills), (b, labelKills)]})
    Jump label arg ->
      let vars = varsSimple arg
          usedAfter = fold $ HashMap.lookup label labelUsedAfter
          usedBefore = usedAfter <> vars
       in (usedBefore, Liveness{varKills = mempty, labelKills = HashMap.singleton label (vars `HashSet.difference` usedAfter)})

livenessInstructions ::
  HashSet Var ->
  [Instruction] ->
  (HashSet Var, Liveness)
livenessInstructions usedAfter insts =
  case insts of
    [] ->
      (usedAfter, mempty)
    inst : insts' ->
      let
        (usedBefore, liveness) = livenessInstructions usedAfter insts'
        (usedBefore', liveness') = livenessInstruction usedBefore inst
       in
        (usedBefore', liveness <> liveness')

livenessBlock ::
  HashMap Label (HashSet Var) ->
  Block ->
  (HashMap Label (HashSet Var), HashSet Var, Liveness)
livenessBlock labelUsedAfter block =
  let
    (usedBefore, liveness) = livenessTerminator labelUsedAfter block.terminator
    (usedBefore', liveness') = livenessInstructions usedBefore block.instructions
   in
    ( HashMap.Lazy.singleton (Label block.name) usedBefore'
    , usedBefore'
    , liveness <> liveness'
    )

livenessBlocks ::
  HashMap Label (HashSet Var) ->
  [Block] ->
  (HashMap Label (HashSet Var), HashSet Var, Liveness)
livenessBlocks finalLabelUsedAfter blocks =
  case blocks of
    [] ->
      mempty
    block : blocks' ->
      let (labelUsedAfter, _usedBefore, liveness) = livenessBlocks finalLabelUsedAfter blocks'
          (labelUsedAfter', usedBefore', liveness') = livenessBlock finalLabelUsedAfter block
       in (labelUsedAfter <> labelUsedAfter', usedBefore', liveness <> liveness')

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