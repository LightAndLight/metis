module Metis.Liveness (liveness, Liveness (..)) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Metis.Anf (Compound (..), Expr (..), Simple (..), Var)

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
liveness = snd . livenessExpr

livenessExpr :: Expr -> (HashSet Var, HashMap Var Liveness)
livenessExpr expr =
  case expr of
    Simple s ->
      case s of
        Var var -> (HashSet.singleton var, mempty)
        Literal{} -> (mempty, mempty)
    LetS var _ value rest ->
      let
        (live, liveAt) = livenessExpr rest
        valueVars = varsSimple value
        live' = HashSet.delete var live `HashSet.union` valueVars
       in
        ( live'
        , HashMap.insert var Liveness{kills = live' `HashSet.difference` live} liveAt
        )
    LetC var _ value rest ->
      let
        (live, liveAt) = livenessExpr rest
        valueVars = varsCompound value
        live' = HashSet.delete var live `HashSet.union` valueVars
       in
        ( live'
        , HashMap.insert var Liveness{kills = live' `HashSet.difference` live} liveAt
        )

varsCompound :: Compound -> HashSet Var
varsCompound compound =
  case compound of
    Binop _ a b -> varsSimple a <> varsSimple b

varsSimple :: Simple -> HashSet Var
varsSimple simple =
  case simple of
    Var var -> HashSet.singleton var
    Literal{} -> mempty