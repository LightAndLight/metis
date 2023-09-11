{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Metis.InstSelectionNew (
  InstSelState (..),
  Var (..),
  Value (..),
  literalToImmediate,
  simpleToValue,
  allocLocal,
  simpleToAddress,
) where

import Control.Monad.State.Class (MonadState, gets, modify)
import Data.Int (Int64)
import Data.Word (Word64)
import Metis.IsaNew (Address (..), AddressBase (..), Immediate (..), Isa, Register, Symbol (..), framePointerRegister)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.SSA (Simple)
import qualified Metis.SSA as SSA
import qualified Metis.SSA.Var as SSA (Var)

data InstSelState = InstSelState {stackFrameTop :: Int64}

data Var isa
  = Virtual SSA.Var
  | -- | A variable that *must* be allocated to a particular register. The variable name is optional: when
    -- supplied, you can provide liveness information about this usage of this register. When the
    -- variable name is omitted, it is considered in use until the end of the program.
    Physical (Maybe SSA.Var) (Register isa)

allocLocal :: forall isa m. (Isa isa, MonadState InstSelState m) => Word64 -> m (Address (Var isa))
allocLocal size = do
  stackFrameTop <- gets (.stackFrameTop)
  let nextStackFrameTop = stackFrameTop - fromIntegral @Word64 @Int64 size
  modify (\s -> s{stackFrameTop = nextStackFrameTop})
  pure Address{base = BaseVar . Physical Nothing $ framePointerRegister @isa, offset = nextStackFrameTop}

data Value isa
  = ValueImmediate Immediate
  | ValueVar (Var isa)

literalToImmediate :: Literal -> Immediate
literalToImmediate l =
  case l of
    Literal.Uint64 w -> Word64 w
    Literal.Bool b -> if b then Word64 1 else Word64 0

simpleToValue :: Simple -> Value isa
simpleToValue simple =
  case simple of
    SSA.Var var ->
      ValueVar $ Virtual var
    SSA.Name name ->
      ValueImmediate . Label $ Symbol name
    SSA.Literal lit ->
      ValueImmediate $ literalToImmediate lit
    SSA.Type _ty ->
      error "TODO: simpleToValue/Type"

simpleToAddress :: Simple -> Address (Var isa)
simpleToAddress simple =
  case simple of
    SSA.Var src ->
      Address{base = BaseVar (Virtual src), offset = 0}
    SSA.Name name ->
      Address{base = BaseLabel $ Symbol name, offset = 0}
    SSA.Literal lit ->
      error $ "literal is not an address: " <> show lit
    SSA.Type _ty ->
      error "TODO: simpleToAddress/Type"