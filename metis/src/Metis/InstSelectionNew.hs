{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

module Metis.InstSelectionNew (
  InstSelEnv (..),
  InstSelState (..),
  initialInstSelState,
  Var (..),
  Value (..),
  literalToImmediate,
  simpleToValue,
  allocLocal,
  simpleToAddress,
  InstSelection (..),
  Block (..),
  instSelectionBlock,
  instSelectionArgs,
  instSelectionReturn,
  Function (..),
  instSelectionFunction,
) where

import Control.Monad ((<=<))
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer.CPS (execWriterT)
import Control.Monad.Writer.Class (MonadWriter, tell)
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Foldable (traverse_)
import Data.Int (Int64)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import Data.Word (Word64)
import Metis.IsaNew (Address (..), AddressBase (..), Immediate (..), Instruction, Isa, Register, Symbol (..), framePointerRegister)
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.SSA (Simple)
import qualified Metis.SSA as SSA
import Metis.SSA.Var (MonadVar)
import qualified Metis.SSA.Var as SSA (Var)
import Metis.Type (Type)
import qualified Metis.Type as Type

data InstSelEnv = InstSelEnv
  { varKinds :: SSA.Var -> Kind
  , nameTys :: Text -> Type SSA.Var
  , varTys :: SSA.Var -> Type SSA.Var
  }

data InstSelState = InstSelState {stackFrameTop :: Int64}

initialInstSelState :: InstSelState
initialInstSelState = InstSelState{stackFrameTop = 0}

data Var isa
  = Virtual SSA.Var
  | -- | A variable that *must* be allocated to a particular register. The variable name is optional: when
    -- supplied, you can provide liveness information about this usage of this register. When the
    -- variable name is omitted, it is considered in use until the end of the program.
    Physical (Maybe SSA.Var) (Register isa)

deriving instance (Isa isa) => Eq (Var isa)
deriving instance (Isa isa) => Show (Var isa)

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

data InstSelection isa m = InstSelection
  { move :: forall var. var -> var -> Instruction isa var
  , selectInstruction :: SSA.Instruction -> m [Instruction isa (Var isa)]
  , selectTerminator :: SSA.Terminator -> m [Instruction isa (Var isa)]
  }

instSelectionArgs ::
  (MonadVar m, MonadWriter (DList (Instruction isa (Var isa))) m) =>
  InstSelection isa m ->
  Seq (Register isa) ->
  [SSA.Var] ->
  [Type SSA.Var] ->
  m ()
instSelectionArgs dict@InstSelection{move} inputRegisters args argTys =
  case (args, argTys) of
    ([], []) ->
      pure ()
    (arg : args', argTy : argTys') ->
      case Type.callingConventionOf argTy of
        Type.Register ->
          case Seq.viewl inputRegisters of
            Seq.EmptyL ->
              error "TODO: instSelectionArgs/Register/EmptyL"
            reg Seq.:< inputRegisters' -> do
              tell . DList.singleton $ move (Physical Nothing reg) (Virtual arg)
              instSelectionArgs dict inputRegisters' args' argTys'
        Type.Composite{} ->
          error "TODO: instSelectionArgs/Composite"
        Type.Erased{} ->
          error "TODO: instSelectionArgs/Erased"
    _ -> error $ "different number of args and arg types: " <> show args <> ", " <> show argTys

instSelectionReturn :: Seq (Register isa) -> SSA.Var -> Type SSA.Var -> Var isa
instSelectionReturn outputRegisters dest retTy =
  case Type.callingConventionOf retTy of
    Type.Register ->
      case Seq.viewl outputRegisters of
        Seq.EmptyL ->
          error "TODO: instSelectionReturn/Register/EmptyL"
        register Seq.:< _outputRegisters' ->
          Physical (Just dest) register
    Type.Composite{} ->
      error "TODO: instSelectionReturn/Composite"
    Type.Erased{} ->
      error "TODO: instSelectionReturn/Erased"

data Block isa var = Block
  { name :: Text
  , instructions :: [Instruction isa var]
  }

deriving instance (Isa isa, Show var) => Show (Block isa var)

instSelectionBlock :: (MonadState InstSelState m) => InstSelection isa m -> SSA.Block -> m (Block isa (Var isa))
instSelectionBlock InstSelection{selectInstruction, selectTerminator} SSA.Block{name, params = _params, instructions, terminator} = do
  instructions' <- execWriterT $ do
    traverse_ (tell . DList.fromList <=< lift . selectInstruction) instructions
    tell . DList.fromList =<< lift (selectTerminator terminator)
  pure Block{name, instructions = DList.toList instructions'}

data Function isa var = Function {name :: Text, blocks :: [Block isa var]}

instSelectionFunction :: (MonadState InstSelState m) => InstSelection isa m -> SSA.Function -> m (Function isa (Var isa))
instSelectionFunction dict function = do
  blocks' <- traverse (instSelectionBlock dict) function.blocks
  pure Function{name = function.name, blocks = blocks'}