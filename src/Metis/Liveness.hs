module Metis.Liveness (liveness, Liveness (..)) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Metis.Anf (Compound (..), Expr (..), Simple (..), Var)

data Liveness = Liveness {before :: HashSet Var, after :: HashSet Var}

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
        , HashMap.insert var Liveness{before = live', after = live} liveAt
        )
    LetC var _ value rest ->
      let
        (live, liveAt) = livenessExpr rest
        valueVars = varsCompound value
        live' = HashSet.delete var live `HashSet.union` valueVars
       in
        ( live'
        , HashMap.insert var Liveness{before = live', after = live} liveAt
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