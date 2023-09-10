{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Metis.RegisterAllocation (
  Virtual (..),
  AnyVirtual (..),
  Physical (..),
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Location (..),
  AllocRegisters (..),
  allocRegisters,
  MockIsa,
  Instruction (..),
  Register (..),
  allocRegistersMockIsa,
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
import Metis.IsaNew (Immediate, Isa (..), Memory (..), MemoryBase (..), sizeOfImmediate)
import Unsafe.Coerce (unsafeCoerce)
import Witherable (wither)

newtype Virtual a = Virtual {value :: Int}
  deriving (Eq, Hashable, Show)

virtualEq :: forall a b. Virtual a -> Virtual b -> Maybe (a :~: b)
virtualEq (Virtual a) (Virtual b) =
  if a == b
    then Just (unsafeCoerce @(a :~: a) @(a :~: b) Refl)
    else Nothing

data Physical :: Type -> Type -> Type where
  Register :: Register isa -> Physical isa (Register isa)
  Memory :: Memory isa -> Word64 -> Physical isa (Memory isa)

deriving instance (Isa isa) => Show (Physical isa a)
deriving instance (Isa isa) => Eq (Physical isa a)

physicalSize :: (Isa isa) => Physical isa a -> Word64
physicalSize (Register reg) = registerSize reg
physicalSize (Memory _mem size) = size

data AllocRegistersEnv = AllocRegistersEnv
  { kills :: HashMap AnyVirtual (HashSet AnyVirtual)
  }

data AllocRegistersState isa = AllocRegistersState
  { locations ::
      forall a.
      Virtual a ->
      Maybe (Location isa a)
  , varSizes :: HashMap AnyVirtual Word64
  , freeRegisters :: Seq (Register isa)
  , occupiedRegisters :: HashMap (Register isa) (Virtual (Register isa))
  , freeMemory :: HashMap Word64 (Seq (Memory isa))
  , stackFrameTop :: Int64
  }

data Location :: Type -> Type -> Type where
  Spilled :: Physical isa (Memory isa) -> Location isa (Register isa)
  NotSpilled :: Physical isa a -> Location isa a

deriving instance (Isa isa) => Show (Location isa a)

data AnyVirtual :: Type where
  AnyVirtual :: Virtual a -> AnyVirtual

instance Eq AnyVirtual where
  AnyVirtual a == AnyVirtual b = a.value == b.value

instance Hashable AnyVirtual where
  hashWithSalt salt (AnyVirtual a) = hashWithSalt salt a.value

getRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Physical isa))) m
  ) =>
  AllocRegisters isa ->
  Virtual (Register isa) ->
  [Virtual (Register isa)] ->
  m (Physical isa (Register isa))
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
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  Virtual (Memory isa) ->
  m (Physical isa (Memory isa))
getMemory var = do
  location <- gets (\AllocRegistersState{locations} -> Maybe.fromMaybe (error $ "virtual " <> show var <> " missing from map") $ locations var)
  case location of
    NotSpilled p ->
      pure p

setPhysical ::
  (Isa isa, MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  Virtual a ->
  Physical isa a ->
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
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  Virtual (Register isa) ->
  Physical isa (Memory isa) ->
  m ()
setSpilled var mem@(Memory _mem size) =
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

setOccupied ::
  (Isa isa, MonadState (AllocRegistersState isa) m) =>
  Physical isa (Register isa) ->
  Virtual (Register isa) ->
  m ()
setOccupied (Register reg) var =
  modify (\s -> s{occupiedRegisters = HashMap.insert reg var s.occupiedRegisters})

allocateRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Physical isa))) m
  ) =>
  AllocRegisters isa ->
  [Virtual (Register isa)] ->
  m (Physical isa (Register isa))
allocateRegister AllocRegisters{store} conflicts = do
  freeRegisters <- gets (.freeRegisters)
  case Seq.viewl freeRegisters of
    Seq.EmptyL -> do
      occupiedRegisters <- gets (.occupiedRegisters)
      conflictingRegisters :: [Register isa] <-
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
        (reg, var :: Virtual (Register isa)) : _ -> do
          mem <- allocateLocal (registerSize reg)

          let occupiedRegister = Register reg
          setSpilled var mem

          tell . DList.singleton $ store mem occupiedRegister
          pure occupiedRegister
    reg Seq.:< freeRegisters' -> do
      let physical = Register reg
      modify (\s -> s{freeRegisters = freeRegisters'})
      pure physical

assignRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  Virtual (Register isa) ->
  Physical isa (Register isa) ->
  m ()
assignRegister var reg = do
  setOccupied reg var
  setPhysical var reg

allocateLocal ::
  forall m isa.
  (Isa isa) =>
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  Word64 ->
  m (Physical isa (Memory isa))
allocateLocal size = do
  freeMemory <- gets (.freeMemory)
  case HashMap.lookup size freeMemory of
    Just (Seq.viewl -> memory Seq.:< memorys) -> do
      modify (\s -> s{freeMemory = HashMap.insert size memorys freeMemory})
      pure $ Memory memory size
    _ -> do
      stackFrameTop <- gets (.stackFrameTop)
      let nextStackFrameTop = stackFrameTop - fromIntegral @Word64 @Int64 size
      modify (\s -> s{stackFrameTop = nextStackFrameTop})
      pure $ Memory Mem{base = BaseRegister $ framePointerRegister @isa, offset = nextStackFrameTop} size

assignLocal ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  Virtual (Memory isa) ->
  Physical isa (Memory isa) ->
  m ()
assignLocal =
  setPhysical

getKilledBy ::
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  Virtual a ->
  m (HashSet AnyVirtual)
getKilledBy var =
  asks (Maybe.fromMaybe mempty . HashMap.lookup (AnyVirtual var) . (.kills))

freeVirtuals ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , Foldable f
  ) =>
  f AnyVirtual ->
  m ()
freeVirtuals vars =
  for_ vars (\(AnyVirtual var) -> freeVirtual var)

freeVirtual ::
  forall isa m a.
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  Virtual a ->
  m ()
freeVirtual var = do
  mLocation <- gets (\AllocRegistersState{locations} -> locations var)
  case mLocation of
    Nothing ->
      error $ "var " <> show var <> " missing from locations map"
    Just location ->
      case location of
        Spilled (Memory mem size) ->
          modify
            ( \s ->
                s
                  { freeMemory =
                      HashMap.insertWith
                        (\new old -> old <> new)
                        size
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
        NotSpilled (Memory mem size) ->
          modify
            ( \s ->
                s
                  { freeMemory =
                      HashMap.insertWith
                        (\new old -> old <> new)
                        size
                        (Seq.singleton mem)
                        s.freeMemory
                  }
            )

data AllocRegisters isa = AllocRegisters
  { traverseVars ::
      forall m var var'.
      (Applicative m) =>
      (forall a. var a -> m (var' a)) ->
      Instruction isa var ->
      m (Instruction isa var')
  , instructionVarInfo :: forall var. (forall a. var a -> Word64) -> Instruction isa var -> Instruction isa (VarInfo isa var)
  , load :: forall var. var (Register isa) -> var (Memory isa) -> Instruction isa var
  , store :: forall var. var (Memory isa) -> var (Register isa) -> Instruction isa var
  }

data VarInfo isa var a
  = VarInfo (Usage var a) (VarType isa a) (var a)

data Usage var a
  = Use [var a]
  | DefReuse (var a)
  | DefNew

data VarType :: Type -> Type -> Type where
  VarReg :: VarType isa (Register isa)
  VarMem :: Word64 -> VarType isa (Memory isa)

allocRegistersVar ::
  forall isa m a.
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Physical isa))) m
  ) =>
  AllocRegisters isa ->
  VarInfo isa Virtual a ->
  m (Physical isa a)
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
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  Instruction isa Virtual ->
  m [Instruction isa (Physical isa)]
allocRegisters1 dict@AllocRegisters{traverseVars, instructionVarInfo} inst = do
  VarSizes f <- varSizesFunction
  (lastInst, insts) <- runWriterT $ traverseVars (allocRegistersVar dict) $ instructionVarInfo f inst
  pure . DList.toList $ insts <> DList.singleton lastInst
  where
    varSizesFunction ::
      (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
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
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  [Instruction isa Virtual] ->
  m [Instruction isa (Physical isa)]
allocRegisters dict =
  fmap concat . traverse (allocRegisters1 dict)

data MockIsa

instance Isa MockIsa where
  pointerSize = 8

  data Register MockIsa = Rax | Rbx | Rcx | Rdx | Rbp
    deriving (Eq, Show, Generic)

  registerSize _ = 8

  registerName Rax = "rax"
  registerName Rbx = "rbx"
  registerName Rcx = "rcx"
  registerName Rdx = "rdx"
  registerName Rbp = "rbp"

  generalPurposeRegisters = Seq.fromList [Rax, Rbx, Rcx, Rdx]

  framePointerRegister = Rbp

  data Instruction MockIsa var
    = Mov_ri (var (Register MockIsa)) Immediate
    | Mov_rm (var (Register MockIsa)) (var (Memory MockIsa))
    | Mov_mi (var (Memory MockIsa)) Immediate
    | Mov_mr (var (Memory MockIsa)) (var (Register MockIsa))
    | Add_ri (var (Register MockIsa)) (var (Register MockIsa)) Immediate
    | Add_rr (var (Register MockIsa)) (var (Register MockIsa)) (var (Register MockIsa))

instance Hashable (Register MockIsa)
deriving instance (forall a. (Show a) => Show (var a)) => Show (Instruction MockIsa var)
deriving instance (forall a. (Eq a) => Eq (var a)) => Eq (Instruction MockIsa var)

allocRegistersMockIsa :: AllocRegisters MockIsa
allocRegistersMockIsa =
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
      Instruction MockIsa var ->
      m (Instruction MockIsa var')
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
      Instruction MockIsa var ->
      Instruction MockIsa (VarInfo MockIsa var)
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
            (VarInfo DefNew (VarMem $ sizeOfImmediate @MockIsa imm) dest)
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