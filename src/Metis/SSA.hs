{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Metis.SSA (
  Expr (..),
  fromCore,
  Compound (..),
  fromCoreCompound,
  Binop (..),
  Simple (..),
  fromCoreSimple,

  -- * Variables
  Var,
  VarInfo (..),
) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Data.Hashable (Hashable)
import Data.Word (Word64)
import qualified Metis.Core as Core
import Metis.Literal (Literal)

newtype Var = MkVar Word64
  deriving (Show, Eq, Hashable)

data VarInfo = VarInfo {size :: Word64}

data Simple
  = SVar Var
  | Literal Literal

data Binop = Add | Subtract

data Compound
  = Simple Simple
  | Binop Binop Simple Simple

data Expr
  = Var Var
  | Let Var VarInfo Compound Expr

varInfo :: Core.Type -> VarInfo
varInfo ty =
  case ty of
    Core.Int8 -> VarInfo{size = 1}
    Core.Int16 -> VarInfo{size = 2}
    Core.Int32 -> VarInfo{size = 4}
    Core.Int64 -> VarInfo{size = 8}
    Core.Uint8 -> VarInfo{size = 1}
    Core.Uint16 -> VarInfo{size = 2}
    Core.Uint32 -> VarInfo{size = 4}
    Core.Uint64 -> VarInfo{size = 8}

fromCore :: Word64 -> (a -> Var) -> Core.Expr a -> Expr
fromCore nextVar toVar expr =
  case expr of
    Core.Var var -> Var (toVar var)
    Core.Let _ ty value rest ->
      let var = MkVar nextVar
       in Let
            var
            (varInfo ty)
            (fromCoreCompound toVar value)
            (fromCore (nextVar + 1) (unvar (\() -> var) toVar) $ fromScope rest)

fromCoreCompound :: (a -> Var) -> Core.Compound a -> Compound
fromCoreCompound toVar compound =
  case compound of
    Core.Simple s ->
      Simple (fromCoreSimple toVar s)
    Core.Add a b ->
      Binop Add (fromCoreSimple toVar a) (fromCoreSimple toVar b)
    Core.Subtract a b ->
      Binop Subtract (fromCoreSimple toVar a) (fromCoreSimple toVar b)

fromCoreSimple :: (a -> Var) -> Core.Simple a -> Simple
fromCoreSimple toVar simple =
  case simple of
    Core.SVar var -> SVar (toVar var)
    Core.Literal lit -> Literal lit