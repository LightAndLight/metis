{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLists #-}

module Metis.InstSelectionNew () where

import Control.Monad.Writer.Class (MonadWriter, tell)
import Data.DList (DList)
import Metis.IsaNew (
  Address (..),
  AddressBase (..),
  Immediate (..),
  Instruction,
  Register,
  Symbol (..),
 )
import Metis.IsaNew.X86_64 (Instruction (..), X86_64)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.SSA (Simple)
import qualified Metis.SSA as SSA
import qualified Metis.SSA.Var as SSA (Var)

data Value isa
  = Literal Literal
  | VarRegister (SSA.Var (Register isa))

instSelection_X86_64 ::
  (MonadWriter (DList (Instruction X86_64 SSA.Var)) m) =>
  SSA.Instruction X86_64 ->
  m (SSA.Var (Register X86_64))
instSelection_X86_64 inst =
  case inst of
    SSA.LetS var ty value -> do
      case value of
        SSA.Var src ->
          tell [Mov_rr var (_ src)]
        SSA.Name name ->
          tell [Mov_ri var (Label $ Symbol name)]
        SSA.Literal lit ->
          tell [Mov_ri var (literalToImmediate lit)]
        SSA.Type ty ->
          _
      pure var
    SSA.LetC var ty operation -> do
      case operation of
        SSA.Binop op a b ->
          case (op, simpleToVarRegister a, simpleToValue b) of
            (SSA.Add, a', b') ->
              case b' of
                Literal b'' ->
                  tell [Add_ri var a' (literalToImmediate b'')]
                VarRegister b'' ->
                  tell [Add_rr var a' b'']
            (SSA.Subtract, a', b') ->
              case b' of
                Literal b'' ->
                  tell [Sub_ri var a' (literalToImmediate b'')]
                VarRegister b'' ->
                  tell [Sub_rr var a' b'']
        SSA.Call f xs -> do
          _ xs
          case f of
            SSA.Var src ->
              tell [Call_r (_ src)]
            SSA.Name name ->
              tell [Call_s (Symbol name)]
            SSA.Literal lit ->
              error $ "can't call literal: " <> show lit
            SSA.Type t ->
              error $ "can't call type: " <> show t
        SSA.Alloca ty ->
          _
        SSA.Store ptr value -> do
          let ptr' = simpleToAddress ptr
          case value of
            SSA.Var src ->
              tell [Mov_mr ptr' (_ src)]
            SSA.Name name ->
              tell [Lea_rs _ (Symbol name), Mov_mr ptr' _]
            SSA.Literal lit ->
              tell [Mov_mi ptr' (literalToImmediate lit)]
            SSA.Type ty ->
              _
        SSA.Load ptr -> do
          let ptr' = simpleToAddress ptr
          tell [Mov_rm var ptr']
        SSA.GetTypeDictField dict field ->
          case field of
            SSA.TypeDictSize -> _
            SSA.TypeDictMove -> _
      pure var

literalToImmediate :: Literal -> Immediate
literalToImmediate l =
  case l of
    Literal.Uint64 w -> Word64 w
    Literal.Bool b -> if b then Word64 1 else Word64 0

simpleToValue :: Simple -> Value isa
simpleToValue simple =
  case simple of
    SSA.Var src ->
      _
    SSA.Name name ->
      _
    SSA.Literal lit ->
      Literal lit
    SSA.Type ty ->
      _

simpleToVarRegister :: Simple -> SSA.Var (Register isa)
simpleToVarRegister simple =
  case simple of
    SSA.Var src ->
      _
    SSA.Name name ->
      _
    SSA.Literal lit ->
      _
    SSA.Type ty ->
      _

simpleToAddress :: Simple -> Address isa
simpleToAddress simple =
  case simple of
    SSA.Var src ->
      _
    SSA.Name name ->
      Address{base = BaseLabel $ Symbol name, offset = 0}
    SSA.Literal lit ->
      error $ "literal is not an address: " <> show lit
    SSA.Type ty ->
      _