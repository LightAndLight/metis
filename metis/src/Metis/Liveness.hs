module Metis.Liveness (liveness, Liveness (..)) where

import Data.Buildable (collectL')
import Data.Foldable (fold)
import qualified Data.HashMap.Lazy as HashMap.Lazy
import qualified Data.HashMap.Lazy as Lazy (HashMap)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Metis.Anf (Compound (..), Expr (..), Simple (..), Var)
import Metis.Type (Type)

-- | Every variable has a 'Liveness' status.
newtype Liveness = Liveness
  { kills :: HashSet Var
  -- ^ The variables that are no longer alive after the target variable has been declared.
  --
  -- e.g.
  --
  -- @
  -- %1 = %2 + %3
  -- @
  --
  -- if @%2@ is not referenced after this instruction, then @%1@ "kills" @%2@.
  }
  deriving (Eq, Show)

liveness :: Expr -> HashMap Var Liveness
liveness expr = liveAt
  where
    (_, liveAt, labelArgVars) = livenessExpr labelArgVars expr

livenessExpr :: Lazy.HashMap Var (HashSet Var) -> Expr -> (HashSet Var, HashMap Var Liveness, Lazy.HashMap Var (HashSet Var))
livenessExpr labelArgVars expr =
  case expr of
    Return s ->
      case s of
        Var var -> (HashSet.singleton var, mempty, mempty)
        Name{} -> (mempty, mempty, mempty)
        Literal{} -> (mempty, mempty, mempty)
        Type{} -> (mempty, mempty, mempty)
    LetS var _ value rest ->
      let
        (live, liveAt, labelArgVars') = livenessExpr labelArgVars rest
        valueVars = varsSimple value
        live' = HashSet.delete var live `HashSet.union` valueVars
       in
        ( live'
        , HashMap.insert var Liveness{kills = live' `HashSet.difference` live} liveAt
        , labelArgVars'
        )
    LetC var _ value rest ->
      let
        (live, liveAt, labelArgVars') = livenessExpr labelArgVars rest
        valueVars = varsCompound value
        live' = HashSet.delete var live `HashSet.union` valueVars
       in
        ( live'
        , HashMap.insert var Liveness{kills = live' `HashSet.difference` live} liveAt
        , labelArgVars'
        )
    IfThenElse cond then_ else_ rest ->
      let
        valueVars = varsSimple cond
        (liveThen, liveAtThen, labelArgVarsThen') = livenessExpr labelArgVars then_
        (liveElse, liveAtElse, labelArgVarsElse') = livenessExpr labelArgVars else_
        (_live, liveAt, labelArgVars') = livenessExpr labelArgVars rest
        live' = liveThen <> liveElse <> valueVars
       in
        ( live'
        , liveAtThen <> liveAtElse <> liveAt
        , HashMap.Lazy.unionWith (<>) labelArgVarsThen' $ HashMap.Lazy.unionWith (<>) labelArgVarsElse' labelArgVars'
        )
    Jump label arg ->
      (varsSimple arg, mempty, HashMap.Lazy.singleton label (varsSimple arg))
    Label label arg rest ->
      let
        (live, liveAt, labelArgVars') = livenessExpr labelArgVars rest
        live' = HashSet.delete arg live
       in
        ( live'
        , -- To figure out which variables `arg` kills, gather every variable
          -- used in `arg_i` for `Jump label arg_i`. All such variables
          -- that aren't in `live` are killed by `arg`.
          HashMap.insert arg Liveness{kills = fold (HashMap.lookup label labelArgVars) `HashSet.difference` live} liveAt
        , labelArgVars'
        )

varsType :: Type Var -> HashSet Var
varsType = collectL'

varsCompound :: Compound -> HashSet Var
varsCompound compound =
  case compound of
    Binop _ a b -> varsSimple a <> varsSimple b
    Call a bs -> varsSimple a <> foldMap varsSimple bs
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