{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Metis.RegisterAllocation (
  Physical (..),
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  Location (..),
  AllocRegisters (..),
  VarInfo (..),
  Usage (..),
  VarType (..),
  allocRegisters,
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
import Data.Int (Int64)
import Data.Kind (Type)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Type.Equality ((:~:) (..))
import Data.Word (Word64)
import Metis.IsaNew (Isa (..), Memory (..), MemoryBase (..))
import qualified Metis.SSA.Var as SSA
import Witherable (wither)

data Physical :: Type -> Type -> Type where
  Register :: Register isa -> Physical isa (Register isa)
  Memory :: Memory isa -> Word64 -> Physical isa (Memory isa)

deriving instance (Isa isa) => Show (Physical isa a)
deriving instance (Isa isa) => Eq (Physical isa a)

physicalSize :: (Isa isa) => Physical isa a -> Word64
physicalSize (Register reg) = registerSize reg
physicalSize (Memory _mem size) = size

data AllocRegistersEnv = AllocRegistersEnv
  { kills :: HashMap SSA.AnyVar (HashSet SSA.AnyVar)
  }

data AllocRegistersState isa = AllocRegistersState
  { locations ::
      forall a.
      SSA.Var a ->
      Maybe (Location isa a)
  , varSizes :: HashMap SSA.AnyVar Word64
  , freeRegisters :: Seq (Register isa)
  , occupiedRegisters :: HashMap (Register isa) (SSA.Var (Register isa))
  , freeMemory :: HashMap Word64 (Seq (Memory isa))
  , stackFrameTop :: Int64
  }

data Location :: Type -> Type -> Type where
  Spilled :: Physical isa (Memory isa) -> Location isa (Register isa)
  NotSpilled :: Physical isa a -> Location isa a

deriving instance (Isa isa) => Show (Location isa a)

getRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Physical isa))) m
  ) =>
  AllocRegisters isa ->
  SSA.Var (Register isa) ->
  [SSA.Var (Register isa)] ->
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
  SSA.Var (Memory isa) ->
  m (Physical isa (Memory isa))
getMemory var = do
  location <- gets (\AllocRegistersState{locations} -> Maybe.fromMaybe (error $ "virtual " <> show var <> " missing from map") $ locations var)
  case location of
    NotSpilled p ->
      pure p

setPhysical ::
  (Isa isa, MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  SSA.Var a ->
  Physical isa a ->
  m ()
setPhysical var physical = do
  modify
    ( \s@AllocRegistersState{locations} ->
        s
          { locations = \var' ->
              case SSA.eqVar var var' of
                Just Refl ->
                  Just $ NotSpilled physical
                Nothing ->
                  locations var'
          , varSizes = HashMap.insert (SSA.AnyVar var) (physicalSize physical) s.varSizes
          }
    )

setSpilled ::
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  SSA.Var (Register isa) ->
  Physical isa (Memory isa) ->
  m ()
setSpilled var mem@(Memory _mem size) =
  modify
    ( \s@AllocRegistersState{locations} ->
        s
          { locations = \var' ->
              case SSA.eqVar var var' of
                Just Refl ->
                  Just $ Spilled mem
                Nothing ->
                  locations var'
          , varSizes = HashMap.insert (SSA.AnyVar var) size s.varSizes
          }
    )

setOccupied ::
  (Isa isa, MonadState (AllocRegistersState isa) m) =>
  Physical isa (Register isa) ->
  SSA.Var (Register isa) ->
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
  [SSA.Var (Register isa)] ->
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
        (reg, var :: SSA.Var (Register isa)) : _ -> do
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
  SSA.Var (Register isa) ->
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
  SSA.Var (Memory isa) ->
  Physical isa (Memory isa) ->
  m ()
assignLocal =
  setPhysical

getKilledBy ::
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  SSA.Var a ->
  m (HashSet SSA.AnyVar)
getKilledBy var =
  asks (Maybe.fromMaybe mempty . HashMap.lookup (SSA.AnyVar var) . (.kills))

freeVars ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , Foldable f
  ) =>
  f SSA.AnyVar ->
  m ()
freeVars vars =
  for_ vars (\(SSA.AnyVar var) -> freeVar var)

freeVar ::
  forall isa m a.
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  SSA.Var a ->
  m ()
freeVar var = do
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
  VarInfo isa SSA.Var a ->
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
      freeVars =<< getKilledBy var

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
      freeVars (HashSet.delete (SSA.AnyVar src) killedByDest)

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

newtype VarSizes = VarSizes (forall a. SSA.Var a -> Word64)

allocRegisters1 ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  Instruction isa SSA.Var ->
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
                    (HashMap.lookup (SSA.AnyVar var) s.varSizes)
              )
        )

allocRegisters ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  [Instruction isa SSA.Var] ->
  m [Instruction isa (Physical isa)]
allocRegisters dict =
  fmap concat . traverse (allocRegisters1 dict)