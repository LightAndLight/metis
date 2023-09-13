{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.IsaNew.X86_64 (
  X86_64,
  Instruction (..),
  Register (..),
  allocRegisters_X86_64,
  instSelection_X86_64,
  printInstruction_X86_64,
) where

import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState)
import Control.Monad.Writer.CPS (execWriterT)
import Control.Monad.Writer.Class (MonadWriter, tell)
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Hashable (Hashable)
import qualified Data.Sequence as Seq
import Data.Text.Lazy.Builder (Builder)
import GHC.Generics (Generic)
import Metis.InstSelectionNew (InstSelEnv (..), InstSelState, InstSelection (..), Value (..), Var (..))
import qualified Metis.InstSelectionNew as InstSelection
import Metis.IsaNew (
  Address (..),
  Immediate (..),
  Instruction,
  Isa (..),
  Register,
  Symbol (..),
  addOffset,
  framePointerRegister,
  printAddress,
  printImmediate,
  printSymbol,
 )
import Metis.RegisterAllocation (AllocRegisters (..), Usage (..), VarInfo (..))
import Metis.SSA (Simple)
import qualified Metis.SSA as SSA
import Metis.SSA.Var (MonadVar, freshVar)
import qualified Metis.Type as Type

data X86_64

instance Isa X86_64 where
  pointerSize = 8

  data Register X86_64
    = Rax
    | Rbx
    | Rcx
    | Rdx
    | Dl
    | Rbp
    | Rsp
    | Rsi
    | Rdi
    | R8
    | R9
    | R10
    | R11
    | R12
    | R13
    | R14
    | R15
    deriving (Eq, Show, Generic)

  registerSize Rax = 8
  registerSize Rbx = 8
  registerSize Rcx = 8
  registerSize Rdx = 8
  registerSize Dl = 1
  registerSize Rbp = 8
  registerSize Rsp = 8
  registerSize Rsi = 8
  registerSize Rdi = 8
  registerSize R8 = 8
  registerSize R9 = 8
  registerSize R10 = 8
  registerSize R11 = 8
  registerSize R12 = 8
  registerSize R13 = 8
  registerSize R14 = 8
  registerSize R15 = 8

  registerName Rax = "rax"
  registerName Rbx = "rbx"
  registerName Rcx = "rcx"
  registerName Rdx = "rdx"
  registerName Dl = "dl"
  registerName Rbp = "rbp"
  registerName Rsp = "rsp"
  registerName Rsi = "rsi"
  registerName Rdi = "rdi"
  registerName R8 = "r8"
  registerName R9 = "r9"
  registerName R10 = "r10"
  registerName R11 = "r11"
  registerName R12 = "r12"
  registerName R13 = "r13"
  registerName R14 = "r14"
  registerName R15 = "r15"

  framePointerRegister = Rbp

  generalPurposeRegisters =
    Seq.fromList
      [ Rax
      , Rbx
      , Rcx
      , Rdx
      , Rsi
      , Rdi
      , R8
      , R9
      , R10
      , R11
      , R12
      , R13
      , R14
      , R15
      ]

  data Instruction X86_64 var
    = Push_r var
    | Push_m (Address var)
    | Push_i Immediate
    | Pop_r var
    | Call_s Symbol
    | Call_r var
    | Je_s Symbol
    | Jmp_s Symbol
    | Jmp_r var
    | Jmp_m (Address var)
    | Ret
    | Ret_i Immediate
    | Mov_ri var Immediate
    | Mov_rr var var
    | Mov_rm var (Address var)
    | Mov_mi (Address var) Immediate
    | Mov_mr (Address var) var
    | Lea_rm var (Address var)
    | Lea_rs var Symbol
    | Cmp_ri var Immediate
    | Cmp_mi (Address var) Immediate
    | Add_ri var var Immediate
    | Add_rr var var var
    | Sub_ri var var Immediate
    | Sub_rr var var var
    deriving (Eq, Show, Functor, Foldable, Traversable)

instance Hashable (Register X86_64)

allocRegisters_X86_64 :: AllocRegisters X86_64
allocRegisters_X86_64 =
  AllocRegisters
    { instructionVarInfo
    , load = Mov_rm
    , store = Mov_mr
    }
  where
    instructionVarInfo ::
      forall var.
      Instruction X86_64 var ->
      Instruction X86_64 (VarInfo var)
    instructionVarInfo inst =
      case inst of
        Push_r a ->
          Push_r (VarInfo (Use []) a)
        Push_m a ->
          Push_m $ fmap (VarInfo (Use [])) a
        Push_i a ->
          Push_i a
        Pop_r a ->
          Pop_r (VarInfo (Use []) a)
        Call_s a ->
          Call_s a
        Call_r a ->
          Call_r (VarInfo (Use []) a)
        Je_s a ->
          Je_s a
        Jmp_s a ->
          Jmp_s a
        Jmp_r a ->
          Jmp_r (VarInfo (Use []) a)
        Jmp_m a ->
          Jmp_m $ fmap (VarInfo (Use [])) a
        Ret ->
          Ret
        Ret_i a ->
          Ret_i a
        Mov_ri a b ->
          Mov_ri (VarInfo DefNew a) b
        Mov_rr a b ->
          Mov_rr (VarInfo DefNew a) (VarInfo (Use []) b)
        Mov_rm a b ->
          Mov_rm (VarInfo DefNew a) (fmap (VarInfo (Use [])) b)
        Mov_mi a b ->
          Mov_mi (fmap (VarInfo (Use [])) a) b
        Mov_mr a b ->
          Mov_mr (fmap (VarInfo (Use [])) a) (VarInfo (Use []) b)
        Lea_rm a b ->
          Lea_rm (VarInfo DefNew a) (fmap (VarInfo (Use [])) b)
        Lea_rs a b ->
          Lea_rs (VarInfo DefNew a) b
        Cmp_ri a b ->
          Cmp_ri (VarInfo (Use []) a) b
        Cmp_mi a b ->
          Cmp_mi (fmap (VarInfo (Use [])) a) b
        Add_ri a b c ->
          Add_ri (VarInfo (DefReuse b) a) (VarInfo (Use []) b) c
        Add_rr a b c ->
          Add_rr (VarInfo (DefReuse b) a) (VarInfo (Use [c]) b) (VarInfo (Use [b]) c)
        Sub_ri a b c ->
          Sub_ri (VarInfo (DefReuse b) a) (VarInfo (Use []) b) c
        Sub_rr a b c ->
          Sub_rr (VarInfo (DefReuse b) a) (VarInfo (Use [c]) b) (VarInfo (Use [b]) c)

instSelection_X86_64 :: (MonadVar m, MonadReader InstSelEnv m, MonadState InstSelState m) => InstSelection X86_64 m
instSelection_X86_64 =
  InstSelection
    { move = Mov_rr
    , selectInstruction = fmap DList.toList . execWriterT . selectInstruction_X86_64
    , selectTerminator = selectTerminator_X86_64
    }

selectInstruction_X86_64 ::
  ( MonadVar m
  , MonadReader InstSelEnv m
  , MonadState InstSelState m
  , MonadWriter (DList (Instruction X86_64 (InstSelection.Var X86_64))) m
  ) =>
  SSA.Instruction ->
  m ()
selectInstruction_X86_64 inst =
  case inst of
    SSA.LetS var _ty value -> do
      case value of
        SSA.Var src ->
          tell [Mov_rr (Virtual var) (Virtual src)]
        SSA.Name name ->
          tell [Lea_rs (Virtual var) (Symbol name)]
        SSA.Literal lit ->
          tell [Mov_ri (Virtual var) (InstSelection.literalToImmediate lit)]
        SSA.Type{} ->
          error "TODO: instSelection/LetS/Type"
    SSA.LetC var _ty operation ->
      case operation of
        SSA.Binop op a b -> do
          a' <- simpleAsVar a
          case (op, InstSelection.simpleToValue b) of
            (SSA.Add, b') ->
              case b' of
                ValueImmediate b'' ->
                  tell [Add_ri (Virtual var) a' b'']
                ValueVar b'' ->
                  tell [Add_rr (Virtual var) a' b'']
            (SSA.Subtract, b') ->
              case b' of
                ValueImmediate b'' ->
                  tell [Sub_ri (Virtual var) a' b'']
                ValueVar b'' ->
                  tell [Sub_rr (Virtual var) a' b'']
        SSA.Call f xs -> do
          varKinds <- asks (.varKinds)
          nameTys <- asks (.nameTys)
          varTys <- asks (.varTys)
          case SSA.typeOf varKinds nameTys varTys f of
            Right (Type.Fn argTys _retTy) -> do
              InstSelection.instSelectionArgs instSelection_X86_64 (generalPurposeRegisters @X86_64) xs argTys
              case f of
                SSA.Var src ->
                  tell [Call_r (Virtual src)]
                SSA.Name name ->
                  tell [Call_s (Symbol name)]
                SSA.Literal lit ->
                  error $ "can't call literal: " <> show lit
                SSA.Type t ->
                  error $ "can't call type: " <> show t
            t ->
              error $ "can't call non-function: " <> show t
        SSA.Alloca t -> do
          addr <- InstSelection.allocLocal @X86_64 $ Type.sizeOf t
          tell [Lea_rm (Virtual var) addr]
        SSA.Store ptr value -> do
          let ptr' = InstSelection.simpleToAddress ptr
          case InstSelection.simpleToValue value of
            ValueImmediate i ->
              tell [Mov_mi ptr' i]
            ValueVar v ->
              tell [Mov_mr ptr' v]
        SSA.Load ptr -> do
          let ptr' = InstSelection.simpleToAddress ptr
          tell [Mov_rm (Virtual var) ptr']
        SSA.GetTypeDictField ptr field -> do
          let ptr' = InstSelection.simpleToAddress ptr
          tell [Mov_rm (Virtual var) (ptr' `addOffset` SSA.typeDictFieldOffset field)]

selectTerminator_X86_64 ::
  ( MonadVar m
  , MonadReader InstSelEnv m
  , MonadState InstSelState m
  ) =>
  SSA.Terminator ->
  m [Instruction X86_64 (InstSelection.Var X86_64)]
selectTerminator_X86_64 term =
  fmap DList.toList . execWriterT $
    case term of
      SSA.Return value -> do
        simpleToVar value (InstSelection.Physical Nothing Rax)
        tell $
          DList.fromList
            [ Pop_r $ InstSelection.Physical Nothing Rbp
            , Ret
            ]
      SSA.IfThenElse cond a b -> do
        var <- simpleAsVar cond
        tell $
          DList.fromList
            [ Cmp_ri var (Word64 0)
            , Je_s $ Symbol b.value
            , Jmp_s $ Symbol a.value
            ]
      SSA.Jump label arg -> do
        _ <- simpleAsVar arg
        tell $
          DList.fromList
            [ Jmp_s . Symbol $ label.value
            ]

simpleToVar ::
  ( MonadVar m
  , MonadWriter (DList (Instruction X86_64 (InstSelection.Var X86_64))) m
  ) =>
  Simple ->
  Var X86_64 ->
  m ()
simpleToVar simple dest =
  case simple of
    SSA.Var var ->
      tell $ DList.fromList [Mov_rr dest (Virtual var) | dest /= Virtual var]
    SSA.Name name ->
      tell . DList.singleton $ Lea_rs dest (Symbol name)
    SSA.Literal lit ->
      tell . DList.singleton $ Mov_ri dest (InstSelection.literalToImmediate lit)
    SSA.Type _ty ->
      error "TODO: simpleAsVar/Type"

simpleAsVar ::
  ( MonadVar m
  , MonadWriter (DList (Instruction X86_64 (InstSelection.Var X86_64))) m
  ) =>
  Simple ->
  m (Var X86_64)
simpleAsVar simple =
  case simple of
    SSA.Var var ->
      pure $ Virtual var
    SSA.Name{} -> do
      dest <- Virtual <$> freshVar
      simpleToVar simple dest
      pure dest
    SSA.Literal{} -> do
      dest <- Virtual <$> freshVar
      simpleToVar simple dest
      pure dest
    SSA.Type _ty -> do
      dest <- Virtual <$> freshVar
      simpleToVar simple dest
      pure dest

printInstruction_X86_64 :: (Eq var, Show var) => (var -> Builder) -> Instruction X86_64 var -> Builder
printInstruction_X86_64 printVar inst =
  case inst of
    Push_r reg ->
      "push " <> printVar reg
    Push_m mem ->
      "push " <> printAddress printVar mem
    Push_i imm ->
      "push " <> printImmediate imm
    Pop_r reg ->
      "pop " <> printVar reg
    Mov_ri a b ->
      "mov " <> printImmediate b <> ", " <> printVar a
    Mov_rr a b ->
      "mov " <> printVar b <> ", " <> printVar a
    Mov_rm a b ->
      "mov " <> printAddress printVar b <> ", " <> printVar a
    Mov_mi a b ->
      "mov " <> printImmediate b <> ", " <> printAddress printVar a
    Mov_mr a b ->
      "mov " <> printVar b <> ", " <> printAddress printVar a
    Lea_rs a b ->
      "lea " <> printSymbol b <> ", " <> printVar a
    Lea_rm a b ->
      "lea " <> printAddress printVar b <> ", " <> printVar a
    Add_ri a b c ->
      if a == b
        then "add " <> printImmediate c <> ", " <> printVar b
        else error $ "instruction has conflicting destinations: " <> show inst
    Add_rr a b c ->
      if a == b
        then "add " <> printVar c <> ", " <> printVar b
        else error $ "instruction has conflicting destinations: " <> show inst
    Sub_ri a b c ->
      if a == b
        then "sub " <> printImmediate c <> ", " <> printVar b
        else error $ "instruction has conflicting destinations: " <> show inst
    Sub_rr a b c ->
      if a == b
        then "sub " <> printVar c <> ", " <> printVar b
        else error $ "instruction has conflicting destinations: " <> show inst
    Call_s sym ->
      "call " <> printSymbol sym
    Call_r reg ->
      "call *" <> printVar reg
    Je_s sym ->
      "je " <> printSymbol sym
    Jmp_s sym ->
      "jmp " <> printSymbol sym
    Jmp_r reg ->
      "jmp *" <> printVar reg
    Jmp_m mem ->
      "jmp *" <> printAddress printVar mem
    Ret ->
      "ret"
    Ret_i i ->
      "ret " <> printImmediate i
    Cmp_ri a b ->
      -- In AT&T syntax, `cmp a, b` returns "greater than" when `b > a`.
      -- `Cmp_ri` keeps its arguments in the actual comparison order, so we have to swap the
      -- operands when generating AT&T syntax.
      "cmp " <> printImmediate b <> ", " <> printVar a
    Cmp_mi a b ->
      "cmp " <> printImmediate b <> ", " <> printAddress printVar a