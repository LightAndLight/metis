{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Metis.RegisterAllocation (
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Inst (..),
  Imm (..),
  Reg (..),
  Mem (..),
  Virtual (..),
  AnyVirtual (..),
  Physical (..),
  allocRegistersInst,
  allocRegistersInsts,
) where

import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Data.Foldable (toList)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable (..))
import Data.Int (Int64)
import Data.Kind (Type)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Traversable (for)
import Data.Type.Equality ((:~:) (..))
import Data.Word (Word64)
import GHC.Generics (Generic)
import Unsafe.Coerce (unsafeCoerce)
import Witherable (wither)

data Reg = Rax | Rbx | Rcx | Rdx | Rbp
  deriving (Eq, Show, Generic)

regSize :: Reg -> Word64
regSize _ = 8

instance Hashable Reg

data Imm = Word64 Word64
  deriving (Eq, Show)

immSize :: Imm -> Word64
immSize Word64{} = 8

data Mem = Mem {base :: Reg, offset :: Int64, size :: Word64}
  deriving (Eq, Show)

newtype Virtual a = Virtual {value :: Int}
  deriving (Eq, Hashable, Show)

virtualEq :: forall a b. Virtual a -> Virtual b -> Maybe (a :~: b)
virtualEq (Virtual a) (Virtual b) =
  if a == b
    then Just (unsafeCoerce @(a :~: a) @(a :~: b) Refl)
    else Nothing

data AnyVirtual :: Type where
  AnyVirtual :: Virtual a -> AnyVirtual

instance Eq AnyVirtual where
  AnyVirtual a == AnyVirtual b = a.value == b.value

instance Hashable AnyVirtual where
  hashWithSalt salt (AnyVirtual a) = hashWithSalt salt a.value

data Physical :: Type -> Type where
  Register :: Reg -> Physical Reg
  Memory :: Mem -> Physical Mem

deriving instance Show (Physical a)
deriving instance Eq (Physical a)

physicalSize :: Physical a -> Word64
physicalSize (Register reg) = regSize reg
physicalSize (Memory mem) = mem.size

data Inst var
  = Mov_ri (var Reg) Imm
  | Mov_rm (var Reg) (var Mem)
  | Mov_mi (var Mem) Imm
  | Mov_mr (var Mem) (var Reg)
  | Add_ri (var Reg) (var Reg) Imm
  | Add_rr (var Reg) (var Reg) (var Reg)

deriving instance (forall a. (Show a) => Show (var a)) => Show (Inst var)
deriving instance (forall a. (Eq a) => Eq (var a)) => Eq (Inst var)

data AllocRegistersEnv = AllocRegistersEnv
  { kills :: HashMap AnyVirtual (HashSet AnyVirtual)
  }

data Location :: Type -> Type where
  Spilled :: Physical Mem -> Location Reg
  NotSpilled :: Physical a -> Location a

deriving instance Show (Location a)

data AllocRegistersState = AllocRegistersState
  { locations ::
      forall a.
      Virtual a ->
      Maybe (Location a)
  , freeRegisters :: Seq Reg
  , occupiedRegisters :: HashMap Reg (Virtual Reg)
  , freeMemory :: HashMap Word64 (Seq Mem)
  , stackFrameTop :: Int64
  }

getRegister ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual Reg ->
  [Virtual Reg] ->
  m ([Inst Physical], Physical Reg)
getRegister var conflicts = do
  location <- gets (\AllocRegistersState{locations} -> Maybe.fromMaybe (error $ "virtual " <> show var <> " missing from map") $ locations var)
  case location of
    Spilled mem -> do
      (insts, reg) <- allocateRegister conflicts
      assignRegister var reg
      pure (insts <> [Mov_rm reg mem], reg)
    NotSpilled p ->
      pure ([], p)

getMemory ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual Mem ->
  m (Physical Mem)
getMemory var = do
  location <- gets (\AllocRegistersState{locations} -> Maybe.fromMaybe (error $ "virtual " <> show var <> " missing from map") $ locations var)
  case location of
    NotSpilled p ->
      pure p

setPhysical ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual a ->
  Physical a ->
  m ()
setPhysical var physical = do
  modify
    ( \s@AllocRegistersState{locations} ->
        s
          { locations = \var' ->
              case virtualEq var var' of
                Just Refl ->
                  Just $ NotSpilled physical
                Nothing ->
                  locations var'
          }
    )

setSpilled ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual Reg ->
  Physical Mem ->
  m ()
setSpilled var mem =
  modify
    ( \s@AllocRegistersState{locations} ->
        s
          { locations = \var' ->
              case virtualEq var var' of
                Just Refl ->
                  Just $ Spilled mem
                Nothing ->
                  locations var'
          }
    )

setOccupied :: (MonadState AllocRegistersState m) => Physical Reg -> Virtual Reg -> m ()
setOccupied (Register reg) var =
  modify (\s -> s{occupiedRegisters = HashMap.insert reg var s.occupiedRegisters})

allocateRegister ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  [Virtual Reg] ->
  m ([Inst Physical], Physical Reg)
allocateRegister conflicts = do
  freeRegisters <- gets (.freeRegisters)
  case Seq.viewl freeRegisters of
    Seq.EmptyL -> do
      occupiedRegisters <- gets (.occupiedRegisters)
      conflictingRegisters :: [Reg] <-
        wither
          ( \v -> do
              mLocation <- gets (\AllocRegistersState{locations} -> locations v)
              case mLocation of
                Nothing ->
                  pure Nothing
                Just Spilled{} ->
                  pure Nothing
                Just (NotSpilled (Register reg)) ->
                  pure $ Just reg
          )
          conflicts
      case filter (\(r, _v) -> r `notElem` conflictingRegisters) $ HashMap.toList occupiedRegisters of
        [] ->
          error "not enough registers"
        (reg, var :: Virtual Reg) : _ -> do
          mem <- allocateLocal (regSize reg)

          let occupiedRegister = Register reg
          setSpilled var mem

          pure ([Mov_mr mem occupiedRegister], occupiedRegister)
    reg Seq.:< freeRegisters' -> do
      let physical = Register reg
      modify (\s -> s{freeRegisters = freeRegisters'})
      pure ([], physical)

assignRegister ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual Reg ->
  Physical Reg ->
  m ()
assignRegister var reg = do
  setOccupied reg var
  setPhysical var reg

allocateLocal ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Word64 ->
  m (Physical Mem)
allocateLocal size = do
  freeMemory <- gets (.freeMemory)
  case HashMap.lookup size freeMemory of
    Just (Seq.viewl -> memory Seq.:< memorys) -> do
      modify (\s -> s{freeMemory = HashMap.insert size memorys freeMemory})
      pure $ Memory memory
    _ -> do
      stackFrameTop <- gets (.stackFrameTop)
      let nextStackFrameTop = stackFrameTop - fromIntegral @Word64 @Int64 size
      modify (\s -> s{stackFrameTop = nextStackFrameTop})
      pure $ Memory Mem{base = Rbp, offset = nextStackFrameTop, size}

assignLocal ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual Mem ->
  Physical Mem ->
  m ()
assignLocal =
  setPhysical

freeVirtual ::
  forall m a.
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual a ->
  m [Inst Physical]
freeVirtual var = do
  mLocation <- gets (\AllocRegistersState{locations} -> locations var)
  case mLocation of
    Nothing ->
      error $ "var " <> show var <> " missing from locations map"
    Just location ->
      case location of
        Spilled (Memory mem) -> do
          modify
            ( \s ->
                s
                  { freeMemory =
                      HashMap.insertWith
                        (\new old -> old <> new)
                        mem.size
                        (Seq.singleton mem)
                        s.freeMemory
                  }
            )
          pure []
        NotSpilled (Register reg) -> do
          modify
            ( \s ->
                s
                  { freeRegisters = reg Seq.<| s.freeRegisters
                  , occupiedRegisters = HashMap.delete reg s.occupiedRegisters
                  }
            )
          pure []
        NotSpilled (Memory mem) -> do
          modify
            ( \s ->
                s
                  { freeMemory =
                      HashMap.insertWith
                        (\new old -> old <> new)
                        mem.size
                        (Seq.singleton mem)
                        s.freeMemory
                  }
            )
          pure []

getKilledBy ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual a ->
  m (HashSet AnyVirtual)
getKilledBy var =
  asks (Maybe.fromMaybe mempty . HashMap.lookup (AnyVirtual var) . (.kills))

freeVirtuals ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m, Foldable f) =>
  f AnyVirtual ->
  m [Inst Physical]
freeVirtuals vars =
  concat <$> for (toList vars) (\(AnyVirtual var) -> freeVirtual var)

allocRegistersInst ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Inst Virtual ->
  m [Inst Physical]
allocRegistersInst inst =
  case inst of
    Mov_ri dest imm -> do
      insts <- freeVirtuals =<< getKilledBy dest

      (insts', dest') <- allocateRegister []
      assignRegister dest dest'
      pure $ insts <> insts' <> [Mov_ri dest' imm]
    Mov_rm dest src -> do
      src' <- getMemory src

      insts <- freeVirtuals =<< getKilledBy dest

      (insts', dest') <- allocateRegister []
      assignRegister dest dest'
      pure $ insts <> insts' <> [Mov_rm dest' src']
    Mov_mi dest imm -> do
      insts <- freeVirtuals =<< getKilledBy dest
      dest' <- allocateLocal (immSize imm)
      assignLocal dest dest'
      pure $ insts <> [Mov_mi dest' imm]
    Mov_mr dest src -> do
      (insts, src') <- getRegister src []

      insts' <- freeVirtuals =<< getKilledBy dest

      dest' <- allocateLocal (physicalSize src')
      assignLocal dest dest'
      pure $ insts <> insts' <> [Mov_mr dest' src']
    Add_ri dest src imm -> do
      (insts', src') <- getRegister src []

      killedByDest <- getKilledBy dest
      insts <- freeVirtuals $ HashSet.delete (AnyVirtual src) killedByDest

      assignRegister dest src'
      pure $ insts <> insts' <> [Add_ri src' src' imm]
    Add_rr dest src1 src2 -> do
      (insts, src1') <- getRegister src1 [src2]
      (insts', src2') <- getRegister src2 [src1]

      killedByDest <- getKilledBy dest
      insts'' <- freeVirtuals $ HashSet.delete (AnyVirtual src1) killedByDest

      assignRegister dest src1'
      pure $ insts <> insts' <> insts'' <> [Add_rr src1' src1' src2']

allocRegistersInsts ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  [Inst Virtual] ->
  m [Inst Physical]
allocRegistersInsts = fmap concat . traverse allocRegistersInst