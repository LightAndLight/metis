{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}

module Metis.Isa.X86_64 (
  X86_64,
  Register (..),
  Instruction (..),
  Inst2 (..),
  simplify_X86_64,
  propagateConstants_X86_64,
  deadCodeElimination_X86_64,

  -- * x86_64 specific instructions
  Movzbq (..),
  Movb (..),
) where

import Control.Monad.State.Class (MonadState, gets, modify, put)
import Control.Monad.State.Strict (evalState)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import qualified Data.Maybe as Maybe
import Data.Word (Word64)
import GHC.Generics (Generic)
import Metis.Asm (Asm (..), Block (..), Statement (..))
import Metis.Isa (
  Add (..),
  Call (..),
  Cmp (..),
  Immediate (..),
  Isa (..),
  Je (..),
  Jmp (..),
  Lea (..),
  Load (..),
  Memory (..),
  MemoryBase (..),
  Mov (..),
  Op2 (..),
  Pop (..),
  Push (..),
  Ret (..),
  Store (..),
  Sub (..),
  Symbol (..),
  Xor (..),
  imm,
 )
import Witherable (wither)

data X86_64

instance Isa X86_64 where
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

  data Instruction X86_64
    = Push_r (Register X86_64)
    | Push_m (Memory X86_64)
    | Push_i Immediate
    | Pop_r (Register X86_64)
    | Call_s Symbol
    | Call_r (Register X86_64)
    | Je_s Symbol
    | Jmp_s Symbol
    | Jmp_r (Register X86_64)
    | Jmp_m (Memory X86_64)
    | Ret
    | Ret_i Immediate
    | Inst2_ir Inst2 (Op2 Immediate (Register X86_64))
    | Inst2_im Inst2 (Op2 Immediate (Memory X86_64))
    | Inst2_rr Inst2 (Op2 (Register X86_64) (Register X86_64))
    | Inst2_rm Inst2 (Op2 (Register X86_64) (Memory X86_64))
    | Inst2_mr Inst2 (Op2 (Memory X86_64) (Register X86_64))
    | Lea_mr (Op2 (Memory X86_64) (Register X86_64))
    | Lea_sr (Op2 Symbol (Register X86_64))
    | Cmp_ri (Register X86_64) Immediate
    | Cmp_mi (Memory X86_64) Immediate
    deriving (Eq, Show)

  registerSize = 8
  framePointerRegister = Rbp

  registerName reg =
    case reg of
      Rax -> "rax"
      Rbx -> "rbx"
      Rcx -> "rcx"
      Rdx -> "rdx"
      Dl -> "dl"
      Rbp -> "rbp"
      Rsp -> "rsp"
      Rsi -> "rsi"
      Rdi -> "rdi"
      R8 -> "r8"
      R9 -> "r9"
      R10 -> "r10"
      R11 -> "r11"
      R12 -> "r12"
      R13 -> "r13"
      R14 -> "r14"
      R15 -> "r15"

  generalPurposeRegisters =
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

instance Hashable (Register X86_64)

data Inst2
  = Mov
  | Movzbq
  | Movb
  | Add
  | Sub
  | Xor
  deriving (Eq, Show)

class Movzbq a b where movzbq :: Op2 a b -> Instruction X86_64
instance Movzbq (Memory X86_64) (Register X86_64) where movzbq = Inst2_mr Movzbq

class Movb a b where movb :: Op2 a b -> Instruction X86_64
instance Movb (Register X86_64) (Memory X86_64) where movb = Inst2_rm Movb

instance Mov X86_64 Immediate (Register X86_64) where mov = Inst2_ir Mov
instance Mov X86_64 (Register X86_64) (Register X86_64) where mov = Inst2_rr Mov
instance Store X86_64 where store = Inst2_rm Mov
instance Load X86_64 where load = Inst2_mr Mov

instance Add X86_64 Immediate (Register X86_64) where add = Inst2_ir Add
instance Add X86_64 Immediate (Memory X86_64) where add = Inst2_im Add
instance Add X86_64 (Register X86_64) (Register X86_64) where add = Inst2_rr Add
instance Add X86_64 (Register X86_64) (Memory X86_64) where add = Inst2_rm Add
instance Add X86_64 (Memory X86_64) (Register X86_64) where add = Inst2_mr Add

instance Sub X86_64 Immediate (Register X86_64) where sub = Inst2_ir Sub
instance Sub X86_64 Immediate (Memory X86_64) where sub = Inst2_im Sub
instance Sub X86_64 (Register X86_64) (Register X86_64) where sub = Inst2_rr Sub
instance Sub X86_64 (Register X86_64) (Memory X86_64) where sub = Inst2_rm Sub
instance Sub X86_64 (Memory X86_64) (Register X86_64) where sub = Inst2_mr Sub

instance Xor X86_64 Immediate (Register X86_64) where xor = Inst2_ir Xor
instance Xor X86_64 Immediate (Memory X86_64) where xor = Inst2_im Xor
instance Xor X86_64 (Register X86_64) (Register X86_64) where xor = Inst2_rr Xor
instance Xor X86_64 (Register X86_64) (Memory X86_64) where xor = Inst2_rm Xor
instance Xor X86_64 (Memory X86_64) (Register X86_64) where xor = Inst2_mr Xor

instance Lea X86_64 (Memory X86_64) (Register X86_64) where lea = Lea_mr
instance Lea X86_64 Symbol (Register X86_64) where lea = Lea_sr

instance Cmp X86_64 (Register X86_64) Immediate where cmp = Cmp_ri
instance Cmp X86_64 (Memory X86_64) Immediate where cmp = Cmp_mi

instance Push X86_64 (Register X86_64) where push = Push_r
instance Push X86_64 (Memory X86_64) where push = Push_m
instance Push X86_64 Immediate where push = Push_i

instance Pop X86_64 (Register X86_64) where pop = Pop_r

instance Call X86_64 Symbol where call = Call_s
instance Call X86_64 (Register X86_64) where call = Call_r

instance Je X86_64 Symbol where je = Je_s

instance Jmp X86_64 Symbol where jmp = Jmp_s
instance Jmp X86_64 (Register X86_64) where jmp = Jmp_r
instance Jmp X86_64 (Memory X86_64) where jmp = Jmp_m

instance Ret X86_64 () where ret () = Ret
instance Ret X86_64 Immediate where ret = Ret_i

simplify_X86_64 :: Asm X86_64 -> Asm X86_64
simplify_X86_64 asm =
  asm
    { text =
        fmap
          ( \block ->
              block
                { statements =
                    deadCodeElimination_X86_64 $ propagateConstants_X86_64 block.statements
                }
          )
          asm.text
    }

data Constant isa
  = Address (Memory isa)
  | Immediate Immediate
  | Unknown

data PropConstState isa = PropConstState
  { registerContents :: HashMap (Register isa) (Constant isa)
  , memoryContents :: HashMap (Memory isa) (Constant isa)
  }

propagateConstants_X86_64 :: [Statement X86_64] -> [Statement X86_64]
propagateConstants_X86_64 =
  flip evalState PropConstState{registerContents = mempty, memoryContents = mempty}
    . traverse propConstStatement

propConstStatement :: (MonadState (PropConstState X86_64) m) => Statement X86_64 -> m (Statement X86_64)
propConstStatement statement =
  case statement of
    Directive{} ->
      pure statement
    Instruction instruction ->
      Instruction <$> propConstInstruction instruction

propConstInstruction :: (MonadState (PropConstState X86_64) m) => Instruction X86_64 -> m (Instruction X86_64)
propConstInstruction inst =
  case inst of
    Inst2_ir Mov Op2{src, dest} -> do
      Immediate src `assignedToRegister` dest
      pure inst
    Inst2_rr Mov Op2{src, dest} -> do
      mSrcContents <- gets (HashMap.lookup src . (.registerContents))
      case mSrcContents of
        Just srcContents -> do
          srcContents `assignedToRegister` dest
          case srcContents of
            Address mem ->
              pure $ Lea_mr Op2{src = mem, dest}
            Immediate i ->
              pure $ Inst2_ir Mov Op2{src = i, dest}
            Unknown ->
              pure inst
        _ -> do
          modify
            ( \s ->
                s
                  { registerContents = HashMap.delete dest s.registerContents
                  , memoryContents = HashMap.filterWithKey (\k _v -> k.base /= BaseRegister dest) s.memoryContents
                  }
            )
          pure inst
    Inst2_mr Mov Op2{src, dest} -> do
      src' <- propConstMemory src
      srcContents <- getMemoryContents src'
      srcContents `assignedToRegister` dest
      case srcContents of
        Address mem ->
          pure $ Lea_mr Op2{src = mem, dest}
        Immediate i ->
          pure $ Inst2_ir Mov Op2{src = i, dest}
        Unknown -> do
          pure inst
    Inst2_im Mov Op2{src, dest} -> do
      dest' <- propConstMemory dest
      Immediate src `assignedToMemory` dest'
      pure $ Inst2_im Mov Op2{src, dest = dest'}
    Inst2_rm Mov Op2{src, dest} -> do
      dest' <- propConstMemory dest
      srcContents <- getRegisterContents src
      srcContents `assignedToMemory` dest'
      case srcContents of
        Address{} ->
          pure inst
        Immediate i ->
          pure $ Inst2_im Mov Op2{src = i, dest = dest'}
        Unknown ->
          pure inst
    Lea_mr Op2{src, dest} -> do
      src' <- propConstMemory src
      Address src' `assignedToRegister` dest
      pure $ Lea_mr Op2{src = src', dest}
    Lea_sr Op2{src, dest} -> do
      Immediate (Label src) `assignedToRegister` dest
      pure inst
    Pop_r dest -> do
      Unknown `assignedToRegister` dest
      pure inst
    Call_s{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    Call_r{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    Je_s{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    Jmp_s{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    Jmp_r{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    Jmp_m mem -> do
      mem' <- propConstMemory mem
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure $ Jmp_m mem'
    Ret{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    Ret_i{} -> do
      put PropConstState{registerContents = mempty, memoryContents = mempty}
      pure inst
    _ ->
      pure inst
  where
    propConstMemory :: (Isa isa, MonadState (PropConstState isa) m) => Memory isa -> m (Memory isa)
    propConstMemory mem =
      case mem.base of
        BaseRegister reg -> do
          mRegContents <- gets (HashMap.lookup reg . (.registerContents))
          case mRegContents of
            Just (Address mem') ->
              pure mem'{offset = mem.offset + mem'.offset}
            _ ->
              pure mem
        BaseLabel{} ->
          pure mem

    getMemoryContents :: (Isa isa, MonadState (PropConstState isa) m) => Memory isa -> m (Constant isa)
    getMemoryContents mem =
      Maybe.fromMaybe Unknown <$> gets (HashMap.lookup mem . (.memoryContents))

    getRegisterContents :: (Isa isa, MonadState (PropConstState isa) m) => Register isa -> m (Constant isa)
    getRegisterContents reg =
      Maybe.fromMaybe Unknown <$> gets (HashMap.lookup reg . (.registerContents))

    assignedToRegister :: (Isa isa, MonadState (PropConstState isa) m) => Constant isa -> Register isa -> m ()
    assignedToRegister src dest = do
      case src of
        Unknown ->
          modify
            ( \s ->
                s
                  { registerContents = HashMap.delete dest s.registerContents
                  , memoryContents = HashMap.filterWithKey (\k _v -> k.base /= BaseRegister dest) s.memoryContents
                  }
            )
        _ ->
          modify
            ( \s ->
                s
                  { registerContents = HashMap.insert dest src s.registerContents
                  , memoryContents = HashMap.filterWithKey (\k _v -> k.base /= BaseRegister dest) s.memoryContents
                  }
            )

    assignedToMemory :: (Isa isa, MonadState (PropConstState isa) m) => Constant isa -> Memory isa -> m ()
    assignedToMemory src dest =
      case src of
        Unknown ->
          modify (\s -> s{memoryContents = HashMap.delete dest s.memoryContents})
        _ ->
          modify (\s -> s{memoryContents = HashMap.insert dest src s.memoryContents})

data DceState isa = DceState
  { registerUsage :: HashMap (Register isa) Word64
  , memoryUsage :: HashMap (Memory isa) Word64
  }

deadCodeElimination_X86_64 :: [Statement X86_64] -> [Statement X86_64]
deadCodeElimination_X86_64 =
  flip evalState DceState{registerUsage = mempty, memoryUsage = mempty}
    . fmap reverse
    . wither dceStatement
    . reverse

dceStatement :: (MonadState (DceState X86_64) m) => Statement X86_64 -> m (Maybe (Statement X86_64))
dceStatement statement =
  case statement of
    Directive{} ->
      pure $ Just statement
    Instruction instruction ->
      fmap Instruction <$> dceInstruction instruction

dceInstruction :: (MonadState (DceState X86_64) m) => Instruction X86_64 -> m (Maybe (Instruction X86_64))
dceInstruction inst =
  case inst of
    Inst2_ir inst2 Op2{src = _, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.registerUsage))
      case inst2 of
        Mov ->
          registerOverwritten dest
        Movb ->
          registerOverwritten dest
        Movzbq ->
          registerOverwritten dest
        Add -> do
          registerOverwritten dest
          registerUsed dest
        Sub -> do
          registerOverwritten dest
          registerUsed dest
        Xor -> do
          registerOverwritten dest
          registerUsed dest
      pure $ if unused then Nothing else Just inst
    Inst2_im inst2 Op2{src = _, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.memoryUsage))

      memoryOverwritten dest
      case inst2 of
        Mov ->
          pure ()
        Movb ->
          pure ()
        Movzbq ->
          pure ()
        Add ->
          memoryUsed dest
        Sub ->
          memoryUsed dest
        Xor ->
          memoryUsed dest

      pure $ if unused then Nothing else Just inst
    Inst2_rr inst2 Op2{src, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.registerUsage))

      registerOverwritten dest
      case inst2 of
        Mov ->
          pure ()
        Movb ->
          pure ()
        Movzbq ->
          pure ()
        Add ->
          registerUsed dest
        Sub ->
          registerUsed dest
        Xor ->
          registerUsed dest
      registerUsed src

      pure $ if unused then Nothing else Just inst
    Inst2_rm inst2 Op2{src, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.memoryUsage))

      memoryOverwritten dest
      case inst2 of
        Mov ->
          pure ()
        Movb ->
          pure ()
        Movzbq ->
          pure ()
        Add ->
          memoryUsed dest
        Sub ->
          memoryUsed dest
        Xor ->
          memoryUsed dest
      registerUsed src

      pure $ if unused then Nothing else Just inst
    Inst2_mr inst2 Op2{src, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.registerUsage))

      registerOverwritten dest
      case inst2 of
        Mov ->
          pure ()
        Movb ->
          pure ()
        Movzbq ->
          pure ()
        Add ->
          registerUsed dest
        Sub ->
          registerUsed dest
        Xor ->
          registerUsed dest
      memoryUsed src

      pure $ if unused then Nothing else Just inst
    Lea_sr Op2{src = _, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.registerUsage))
      registerOverwritten dest
      pure $ if unused then Nothing else Just inst
    Lea_mr Op2{src, dest} -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.registerUsage))
      addressUsed src
      registerOverwritten dest
      pure $ if unused then Nothing else Just inst
    Push_r reg -> do
      registerUsed reg
      pure $ Just inst
    Push_m mem -> do
      memoryUsed mem
      pure $ Just inst
    Push_i{} ->
      pure $ Just inst
    Pop_r dest -> do
      unused <- gets ((== Just 0) . HashMap.lookup dest . (.registerUsage))
      registerOverwritten dest
      if unused
        then pure . Just $ sub Op2{src = imm (8 :: Word64), dest = Rsp}
        else pure $ Just inst
    Call_s{} -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      pure $ Just inst
    Call_r{} -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      pure $ Just inst
    Je_s{} -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      pure $ Just inst
    Jmp_s{} -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      pure $ Just inst
    Jmp_r reg -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      registerUsed reg
      pure $ Just inst
    Jmp_m mem -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      memoryUsed mem
      pure $ Just inst
    Ret -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      pure $ Just inst
    Ret_i{} -> do
      modify (\s -> s{registerUsage = mempty, memoryUsage = mempty})
      pure $ Just inst
    Cmp_ri reg _ -> do
      registerUsed reg
      pure $ Just inst
    Cmp_mi mem _ -> do
      memoryUsed mem
      pure $ Just inst
  where
    registerOverwritten :: (MonadState (DceState X86_64) m) => Register X86_64 -> m ()
    registerOverwritten reg =
      modify
        ( \s ->
            s
              { registerUsage = HashMap.insert reg 0 s.registerUsage
              , memoryUsage = HashMap.filterWithKey (\k _v -> k.base /= BaseRegister reg) s.memoryUsage
              }
        )

    registerUsed :: (MonadState (DceState X86_64) m) => Register X86_64 -> m ()
    registerUsed reg =
      modify (\s -> s{registerUsage = HashMap.insertWith (+) reg 1 s.registerUsage})

    addressUsed :: (MonadState (DceState X86_64) m) => Memory X86_64 -> m ()
    addressUsed mem =
      case mem.base of
        BaseRegister reg ->
          registerUsed reg
        _ ->
          pure ()

    memoryOverwritten :: (MonadState (DceState X86_64) m) => Memory X86_64 -> m ()
    memoryOverwritten mem = do
      modify (\s -> s{memoryUsage = HashMap.insert mem 0 s.memoryUsage})
      addressUsed mem

    memoryUsed :: (MonadState (DceState X86_64) m) => Memory X86_64 -> m ()
    memoryUsed mem = do
      modify (\s -> s{memoryUsage = HashMap.insertWith (+) mem 1 s.memoryUsage})
      addressUsed mem