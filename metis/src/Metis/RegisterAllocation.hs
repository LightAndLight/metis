{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Metis.RegisterAllocation (
  Imm (..),
  Reg (..),
  Mem (..),
  Virtual (..),
  AnyVirtual (..),
  Physical (..),
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Location (..),
  AllocRegisters (..),
  allocRegisters,
  Inst (..),
  allocRegistersInst,
) where

import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.Trans.Writer.CPS (runWriterT)
import Control.Monad.Writer.Class (MonadWriter, tell)
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Foldable (for_)
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

data Physical :: Type -> Type where
  Register :: Reg -> Physical Reg
  Memory :: Mem -> Physical Mem

deriving instance Show (Physical a)
deriving instance Eq (Physical a)

physicalSize :: Physical a -> Word64
physicalSize (Register reg) = regSize reg
physicalSize (Memory mem) = mem.size

data AllocRegistersEnv = AllocRegistersEnv
  { kills :: HashMap AnyVirtual (HashSet AnyVirtual)
  }

data AllocRegistersState = AllocRegistersState
  { locations ::
      forall a.
      Virtual a ->
      Maybe (Location a)
  , varSizes :: HashMap AnyVirtual Word64
  , freeRegisters :: Seq Reg
  , occupiedRegisters :: HashMap Reg (Virtual Reg)
  , freeMemory :: HashMap Word64 (Seq Mem)
  , stackFrameTop :: Int64
  }

data Location :: Type -> Type where
  Spilled :: Physical Mem -> Location Reg
  NotSpilled :: Physical a -> Location a

deriving instance Show (Location a)

data AnyVirtual :: Type where
  AnyVirtual :: Virtual a -> AnyVirtual

instance Eq AnyVirtual where
  AnyVirtual a == AnyVirtual b = a.value == b.value

instance Hashable AnyVirtual where
  hashWithSalt salt (AnyVirtual a) = hashWithSalt salt a.value

getRegister ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m, MonadWriter (DList (inst Physical)) m) =>
  AllocRegisters inst ->
  Virtual Reg ->
  [Virtual Reg] ->
  m (Physical Reg)
getRegister dict@AllocRegisters{load} var conflicts = do
  location <- gets (\AllocRegistersState{locations} -> Maybe.fromMaybe (error $ "virtual " <> show var <> " missing from map") $ locations var)
  case location of
    Spilled mem -> do
      reg <- allocateRegister dict conflicts
      assignRegister var reg
      tell . DList.singleton $ load reg mem
      pure reg
    NotSpilled p ->
      pure p

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
          , varSizes = HashMap.insert (AnyVirtual var) (physicalSize physical) s.varSizes
          }
    )

setSpilled ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual Reg ->
  Physical Mem ->
  m ()
setSpilled var mem@(Memory Mem{size}) =
  modify
    ( \s@AllocRegistersState{locations} ->
        s
          { locations = \var' ->
              case virtualEq var var' of
                Just Refl ->
                  Just $ Spilled mem
                Nothing ->
                  locations var'
          , varSizes = HashMap.insert (AnyVirtual var) size s.varSizes
          }
    )

setOccupied :: (MonadState AllocRegistersState m) => Physical Reg -> Virtual Reg -> m ()
setOccupied (Register reg) var =
  modify (\s -> s{occupiedRegisters = HashMap.insert reg var s.occupiedRegisters})

allocateRegister ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m, MonadWriter (DList (inst Physical)) m) =>
  AllocRegisters inst ->
  [Virtual Reg] ->
  m (Physical Reg)
allocateRegister AllocRegisters{store} conflicts = do
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

          tell . DList.singleton $ store mem occupiedRegister
          pure occupiedRegister
    reg Seq.:< freeRegisters' -> do
      let physical = Register reg
      modify (\s -> s{freeRegisters = freeRegisters'})
      pure physical

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

getKilledBy ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual a ->
  m (HashSet AnyVirtual)
getKilledBy var =
  asks (Maybe.fromMaybe mempty . HashMap.lookup (AnyVirtual var) . (.kills))

freeVirtuals ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m, Foldable f) =>
  f AnyVirtual ->
  m ()
freeVirtuals vars =
  for_ vars (\(AnyVirtual var) -> freeVirtual var)

freeVirtual ::
  forall m a.
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  Virtual a ->
  m ()
freeVirtual var = do
  mLocation <- gets (\AllocRegistersState{locations} -> locations var)
  case mLocation of
    Nothing ->
      error $ "var " <> show var <> " missing from locations map"
    Just location ->
      case location of
        Spilled (Memory mem) ->
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
        NotSpilled (Register reg) ->
          modify
            ( \s ->
                s
                  { freeRegisters = reg Seq.<| s.freeRegisters
                  , occupiedRegisters = HashMap.delete reg s.occupiedRegisters
                  }
            )
        NotSpilled (Memory mem) ->
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

data AllocRegisters inst = AllocRegisters
  { traverseVars ::
      forall m var var'.
      (Applicative m) =>
      (forall a. var a -> m (var' a)) ->
      inst var ->
      m (inst var')
  , instructionVarInfo :: forall var. (forall a. var a -> Word64) -> inst var -> inst (VarInfo var)
  , load :: forall var. var Reg -> var Mem -> inst var
  , store :: forall var. var Mem -> var Reg -> inst var
  }

data VarInfo var a
  = VarInfo (Usage var a) (VarType a) (var a)

data Usage var a
  = Use [var a]
  | DefReuse (var a)
  | DefNew

data VarType :: Type -> Type where
  VarReg :: VarType Reg
  VarMem :: Word64 -> VarType Mem

allocRegistersVar ::
  forall m a inst.
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m, MonadWriter (DList (inst Physical)) m) =>
  AllocRegisters inst ->
  VarInfo Virtual a ->
  m (Physical a)
allocRegistersVar dict (VarInfo info varType var) =
  case info of
    Use conflicts ->
      case varType of
        VarMem _size ->
          getMemory var
        VarReg ->
          getRegister dict var conflicts
    DefNew -> do
      freeVirtuals =<< getKilledBy var

      case varType of
        VarReg -> do
          dest <- allocateRegister dict []
          assignRegister var dest
          pure dest
        VarMem size -> do
          dest <- allocateLocal size
          assignLocal var dest
          pure dest
    DefReuse src -> do
      src' <-
        case varType of
          VarReg ->
            getRegister dict src []
          VarMem _size ->
            getMemory src

      killedByDest <- getKilledBy var
      freeVirtuals (HashSet.delete (AnyVirtual src) killedByDest)

      let
        {-# INLINE assign #-}
        assign =
          case varType of
            VarReg ->
              assignRegister var src'
            VarMem _size ->
              assignLocal var src'

      -- I need to give this expression a type signature, and `fourmolu` crashes if I parenthesise
      -- the `case` expression and give it a type. Factoring out the expression fixes it.
      assign :: m ()

      pure src'

newtype VarSizes = VarSizes (forall a. Virtual a -> Word64)

allocRegisters1 ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  AllocRegisters inst ->
  inst Virtual ->
  m [inst Physical]
allocRegisters1 dict@AllocRegisters{traverseVars, instructionVarInfo} inst = do
  VarSizes f <- varSizesFunction
  (lastInst, insts) <- runWriterT $ traverseVars (allocRegistersVar dict) $ instructionVarInfo f inst
  pure . DList.toList $ insts <> DList.singleton lastInst
  where
    varSizesFunction ::
      (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
      m VarSizes
    varSizesFunction =
      gets
        ( \s ->
            VarSizes
              ( \var ->
                  Maybe.fromMaybe
                    (error $ "var " <> show var <> " not in sizes map")
                    (HashMap.lookup (AnyVirtual var) s.varSizes)
              )
        )

allocRegisters ::
  (MonadReader AllocRegistersEnv m, MonadState AllocRegistersState m) =>
  AllocRegisters inst ->
  [inst Virtual] ->
  m [inst Physical]
allocRegisters dict =
  fmap concat . traverse (allocRegisters1 dict)

data Inst var
  = Mov_ri (var Reg) Imm
  | Mov_rm (var Reg) (var Mem)
  | Mov_mi (var Mem) Imm
  | Mov_mr (var Mem) (var Reg)
  | Add_ri (var Reg) (var Reg) Imm
  | Add_rr (var Reg) (var Reg) (var Reg)

deriving instance (forall a. (Show a) => Show (var a)) => Show (Inst var)
deriving instance (forall a. (Eq a) => Eq (var a)) => Eq (Inst var)

allocRegistersInst :: AllocRegisters Inst
allocRegistersInst =
  AllocRegisters
    { traverseVars
    , instructionVarInfo
    , load = Mov_rm
    , store = Mov_mr
    }
  where
    traverseVars ::
      (Applicative m) =>
      (forall a. var a -> m (var' a)) ->
      Inst var ->
      m (Inst var')
    traverseVars f inst =
      case inst of
        Mov_ri dest imm ->
          (\dest' -> Mov_ri dest' imm) <$> f dest
        Mov_rm dest src ->
          (\src' dest' -> Mov_rm dest' src') <$> f src <*> f dest
        Mov_mi dest imm -> do
          (\dest' -> Mov_mi dest' imm) <$> f dest
        Mov_mr dest src -> do
          (\src' dest' -> Mov_mr dest' src') <$> f src <*> f dest
        Add_ri dest src imm -> do
          (\src' dest' -> Add_ri dest' src' imm) <$> f src <*> f dest
        Add_rr dest src1 src2 -> do
          (\src1' src2' dest' -> Add_rr dest' src1' src2') <$> f src1 <*> f src2 <*> f dest

    instructionVarInfo ::
      (forall a. var a -> Word64) ->
      Inst var ->
      Inst (VarInfo var)
    instructionVarInfo varSize inst =
      case inst of
        Mov_ri dest imm ->
          Mov_ri
            (VarInfo DefNew VarReg dest)
            imm
        Mov_rm dest src ->
          Mov_rm
            (VarInfo DefNew VarReg dest)
            (VarInfo (Use []) (VarMem $ varSize src) src)
        Mov_mi dest imm ->
          Mov_mi
            (VarInfo DefNew (VarMem $ immSize imm) dest)
            imm
        Mov_mr dest src ->
          Mov_mr
            (VarInfo DefNew (VarMem $ varSize src) dest)
            (VarInfo (Use []) VarReg src)
        Add_ri dest src imm ->
          Add_ri
            (VarInfo (DefReuse src) VarReg dest)
            (VarInfo (Use []) VarReg src)
            imm
        Add_rr dest src1 src2 ->
          Add_rr
            (VarInfo (DefReuse src1) VarReg dest)
            (VarInfo (Use [src2]) VarReg src1)
            (VarInfo (Use [src1]) VarReg src2)