{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}

module Metis.LivenessNew (
  LivenessT,
  runLivenessT,
  Liveness (..),
  livenessBlocks,
  livenessBlock,
  livenessInstructions,
  livenessInstruction,
  livenessTerminator,
) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (MonadReader, ask)
import Control.Monad.Trans.Writer.CPS (runWriterT)
import Control.Monad.Writer.CPS (WriterT)
import Control.Monad.Writer.Class (tell)
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

tellVarKills :: (Monad m) => Var -> HashSet Var -> LivenessT m ()
tellVarKills var vars =
  LivenessT $
    tell
      ( mempty
      , mempty
          { varKills = if HashSet.null vars then mempty else HashMap.singleton var vars
          }
      )

tellLabelKills :: (Monad m) => Label -> HashSet Var -> LivenessT m ()
tellLabelKills label vars =
  LivenessT $
    tell
      ( mempty
      , mempty
          { labelKills = if HashSet.null vars then mempty else HashMap.singleton label vars
          }
      )

tellUsedAfterLabel :: (Monad m) => Label -> HashSet Var -> LivenessT m ()
tellUsedAfterLabel label vars =
  LivenessT $ tell (HashMap.Lazy.singleton label vars, mempty)

livenessInstruction ::
  (Monad m) =>
  HashSet Var ->
  Instruction ->
  LivenessT m (HashSet Var)
livenessInstruction usedAfter inst =
  case inst of
    LetS var _ value -> do
      let valueVars = varsSimple value
          usedBefore = HashSet.delete var usedAfter <> valueVars
          varKills = valueVars `HashSet.difference` usedAfter

      tellVarKills var varKills

      pure usedBefore
    LetC var _ value -> do
      let valueVars = varsCompound value
          usedBefore = HashSet.delete var usedAfter <> valueVars

          varKills = valueVars `HashSet.difference` usedAfter

      tellVarKills var varKills

      pure usedBefore

livenessTerminator ::
  (Monad m) =>
  Terminator ->
  LivenessT m (HashSet Var)
livenessTerminator term =
  case term of
    Return value -> do
      let usedBefore = varsSimple value
      pure usedBefore
    IfThenElse cond a b -> do
      usedAfterLabel <- ask

      let vars = varsSimple cond
          aUsedAfter = fold $ HashMap.lookup a usedAfterLabel
          bUsedAfter = fold $ HashMap.lookup b usedAfterLabel
          abUsedAfter = aUsedAfter <> bUsedAfter
          usedBefore = abUsedAfter <> vars
          labelKills = vars `HashSet.difference` abUsedAfter

      tellLabelKills a labelKills
      tellLabelKills b labelKills

      pure usedBefore
    Jump label arg -> do
      usedAfterLabel <- ask

      let vars = varsSimple arg
          usedAfter = fold $ HashMap.lookup label usedAfterLabel
          usedBefore = usedAfter <> vars
          labelKills = vars `HashSet.difference` usedAfter

      tellLabelKills label labelKills

      pure usedBefore

livenessInstructions ::
  (Monad m) =>
  HashSet Var ->
  [Instruction] ->
  LivenessT m (HashSet Var)
livenessInstructions usedAfter insts =
  case insts of
    [] ->
      pure usedAfter
    inst : insts' -> do
      usedBefore <- livenessInstructions usedAfter insts'
      livenessInstruction usedBefore inst

livenessBlock ::
  (Monad m) =>
  Block ->
  LivenessT m (HashSet Var)
livenessBlock block = do
  usedBefore <- livenessTerminator block.terminator
  usedBefore' <- livenessInstructions usedBefore block.instructions
  tellUsedAfterLabel (Label block.name) usedBefore'
  pure usedBefore'

livenessBlocks ::
  (Monad m) =>
  [Block] ->
  LivenessT m (HashSet Var)
livenessBlocks blocks =
  case blocks of
    [] ->
      pure mempty
    block : blocks' -> do
      _usedBefore <- livenessBlocks blocks'
      livenessBlock block

newtype LivenessT m a
  = LivenessT
      ( ReaderT
          (HashMap Label (HashSet Var))
          (WriterT (HashMap Label (HashSet Var), Liveness) m)
          a
      )
  deriving (Functor, Applicative, Monad, MonadReader (HashMap Label (HashSet Var)))

runLivenessT :: (MonadFix m) => LivenessT m a -> m (Liveness, a)
runLivenessT (LivenessT ma) = do
  rec (a, (labelUsedAfterFinal, liveness)) <- runWriterT $ runReaderT ma labelUsedAfterFinal
  pure (liveness, a)

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