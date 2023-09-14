{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
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
  AllocRegistersEnv (..),
  AllocRegistersState (..),
  initialAllocRegistersState,
  Location (..),
  AllocRegisters (..),
  VarInfo (..),
  Usage (..),
  allocRegisters,
  allocRegistersBlock,
  allocRegistersFunction,
) where

import Control.Lens.Cons (uncons)
import Control.Monad ((<=<))
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
import Data.Word (Word64)
import qualified Metis.InstSelectionNew as InstSelection
import Metis.IsaNew (Address (..), AddressBase (..), Isa (..))
import Metis.LivenessNew (Liveness (..))
import qualified Metis.SSA.Var as SSA
import Witherable (wither)

data AllocRegistersEnv = AllocRegistersEnv
  { liveness :: Liveness
  }

data AllocRegistersState isa = AllocRegistersState
  { locations :: HashMap SSA.Var (Location isa)
  , varSizes :: HashMap SSA.Var Word64
  , freeRegisters :: Seq (Register isa)
  , occupiedRegisters :: HashMap (Register isa) SSA.Var
  , freeMemory :: HashMap Word64 (Seq (Address (Register isa)))
  , stackFrameTop :: Int64
  }

initialAllocRegistersState :: forall isa. (Isa isa) => AllocRegistersState isa
initialAllocRegistersState =
  AllocRegistersState
    { locations = mempty
    , varSizes = mempty
    , freeRegisters = generalPurposeRegisters @isa
    , occupiedRegisters = mempty
    , freeMemory = mempty
    , stackFrameTop = 0
    }

data Location :: Type -> Type where
  Spilled :: Address (Register isa) -> Word64 -> Location isa
  NotSpilled :: Register isa -> Location isa

deriving instance (Isa isa) => Show (Location isa)

getRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Register isa))) m
  ) =>
  AllocRegisters isa ->
  SSA.Var ->
  [InstSelection.Var isa] ->
  m (Register isa)
getRegister dict@AllocRegisters{load} var conflicts = do
  location <-
    gets
      ( \s ->
          Maybe.fromMaybe
            (error $ "virtual " <> show var <> " missing from map")
            (HashMap.lookup var s.locations)
      )
  case location of
    Spilled mem _ -> do
      reg <- allocateRegister dict uncons conflicts
      assignRegister var reg
      tell . DList.singleton $ load reg mem
      pure reg
    NotSpilled p ->
      pure p

setPhysical ::
  (Isa isa, MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  SSA.Var ->
  Register isa ->
  m ()
setPhysical var physical = do
  modify
    ( \s ->
        s
          { locations = HashMap.insert var (NotSpilled physical) s.locations
          , varSizes = HashMap.insert var (registerSize physical) s.varSizes
          }
    )

setSpilled ::
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  SSA.Var ->
  Address (Register isa) ->
  Word64 ->
  m ()
setSpilled var mem size =
  modify
    ( \s ->
        s
          { locations = HashMap.insert var (Spilled mem size) s.locations
          , varSizes = HashMap.insert var size s.varSizes
          }
    )

setOccupied ::
  (Isa isa, MonadState (AllocRegistersState isa) m) =>
  Register isa ->
  SSA.Var ->
  m ()
setOccupied reg var =
  modify (\s -> s{occupiedRegisters = HashMap.insert reg var s.occupiedRegisters})

allocateRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Register isa))) m
  ) =>
  AllocRegisters isa ->
  (Seq (Register isa) -> Maybe (Register isa, Seq (Register isa))) ->
  [InstSelection.Var isa] ->
  m (Register isa)
allocateRegister AllocRegisters{store} get conflicts = do
  freeRegisters <- gets (.freeRegisters)
  case get freeRegisters of
    Nothing -> do
      occupiedRegisters <- gets (.occupiedRegisters)
      conflictingRegisters :: [Register isa] <-
        wither
          ( \case
              InstSelection.Physical _ reg ->
                pure $ Just reg
              InstSelection.Virtual virtual -> do
                mLocation <- gets (HashMap.lookup virtual . (.locations))
                case mLocation of
                  Nothing ->
                    pure Nothing
                  Just Spilled{} ->
                    pure Nothing
                  Just (NotSpilled reg) ->
                    pure $ Just reg
          )
          conflicts
      case filter (\(r, _v) -> r `notElem` conflictingRegisters) $ HashMap.toList occupiedRegisters of
        [] ->
          error "not enough registers"
        (reg, var :: SSA.Var) : _ -> do
          let size = registerSize reg
          mem <- allocateLocal size

          setSpilled var mem size

          tell . DList.singleton $ store mem reg
          pure reg
    Just (reg, freeRegisters') -> do
      modify (\s -> s{freeRegisters = freeRegisters'})
      pure reg

assignRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  SSA.Var ->
  Register isa ->
  m ()
assignRegister var reg = do
  setOccupied reg var
  setPhysical var reg

allocateLocal ::
  forall m isa.
  (Isa isa) =>
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  Word64 ->
  m (Address (Register isa))
allocateLocal size = do
  freeMemory <- gets (.freeMemory)
  case HashMap.lookup size freeMemory of
    Just (Seq.viewl -> memory Seq.:< memorys) -> do
      modify (\s -> s{freeMemory = HashMap.insert size memorys freeMemory})
      pure memory
    _ -> do
      stackFrameTop <- gets (.stackFrameTop)
      let nextStackFrameTop = stackFrameTop - fromIntegral @Word64 @Int64 size
      modify (\s -> s{stackFrameTop = nextStackFrameTop})
      pure Address{base = BaseVar $ framePointerRegister @isa, offset = nextStackFrameTop}

getKilledBy ::
  (MonadReader AllocRegistersEnv m, MonadState (AllocRegistersState isa) m) =>
  SSA.Var ->
  m (HashSet SSA.Var)
getKilledBy var =
  asks (Maybe.fromMaybe mempty . HashMap.lookup var . (.varKills) . (.liveness))

freeVars ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , Foldable f
  ) =>
  f SSA.Var ->
  m ()
freeVars vars =
  for_ vars freeVar

freeVar ::
  forall isa m.
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  SSA.Var ->
  m ()
freeVar var = do
  mLocation <- gets (HashMap.lookup var . (.locations))
  case mLocation of
    Nothing ->
      error $ "var " <> show var <> " missing from locations map"
    Just location ->
      case location of
        Spilled mem size ->
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
        NotSpilled reg ->
          modify
            ( \s ->
                s
                  { freeRegisters = reg Seq.<| s.freeRegisters
                  , occupiedRegisters = HashMap.delete reg s.occupiedRegisters
                  }
            )

data AllocRegisters isa = AllocRegisters
  { instructionVarInfo :: forall var. Instruction isa var -> Instruction isa (VarInfo var)
  , load :: forall var. var -> Address var -> Instruction isa var
  , store :: forall var. Address var -> var -> Instruction isa var
  }

data VarInfo var
  = VarInfo (Usage var) var

data Usage var
  = Use [var]
  | DefReuse var
  | DefNew

allocRegistersVar ::
  forall isa m.
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Register isa))) m
  ) =>
  AllocRegisters isa ->
  VarInfo (InstSelection.Var isa) ->
  m (Register isa)
allocRegistersVar dict (VarInfo info var) =
  case var of
    InstSelection.Physical mVirtual physical -> do
      for_ mVirtual $ freeVars <=< getKilledBy
      dest <-
        allocateRegister
          dict
          ( \available -> do
              index <- Seq.findIndexL (== physical) available
              let (prefix, suffix) = Seq.splitAt index available
              case Seq.viewl suffix of
                Seq.EmptyL ->
                  Nothing
                register Seq.:< registers ->
                  Just (register, prefix <> registers)
          )
          []
      for_ mVirtual $ \virtual -> assignRegister virtual dest
      pure dest
    InstSelection.Virtual virtual ->
      case info of
        Use conflicts ->
          getRegister dict virtual conflicts
        DefNew -> do
          freeVars =<< getKilledBy virtual

          dest <- allocateRegister dict uncons []
          assignRegister virtual dest
          pure dest
        DefReuse src -> do
          reg <-
            case src of
              InstSelection.Physical mVar srcPhysical -> do
                killedByDest <- getKilledBy virtual
                freeVars $ maybe id HashSet.delete mVar killedByDest

                pure srcPhysical
              InstSelection.Virtual srcVirtual -> do
                src' <- getRegister dict srcVirtual []

                killedByDest <- getKilledBy virtual
                freeVars (HashSet.delete srcVirtual killedByDest)

                pure src'

          assignRegister virtual reg
          pure reg

allocRegisters1 ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  Instruction isa (InstSelection.Var isa) ->
  m [Instruction isa (Register isa)]
allocRegisters1 dict@AllocRegisters{instructionVarInfo} inst = do
  (lastInst, insts) <-
    runWriterT
      -- Is it okay to traverse "defs" before "uses"?
      -- When writing instructions in Intel style, the destination goes before the sources. This
      -- means it's traversed before the sources.
      . traverse (allocRegistersVar dict)
      $ instructionVarInfo inst
  pure . DList.toList $ insts <> DList.singleton lastInst

allocRegisters ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  [Instruction isa (InstSelection.Var isa)] ->
  m [Instruction isa (Register isa)]
allocRegisters dict =
  fmap concat . traverse (allocRegisters1 dict)

allocRegistersBlock ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  InstSelection.Block isa (InstSelection.Var isa) ->
  m (InstSelection.Block isa (Register isa))
allocRegistersBlock dict block = do
  instructions' <- allocRegisters dict block.instructions
  pure block{InstSelection.instructions = instructions'}

allocRegistersFunction ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  ) =>
  AllocRegisters isa ->
  InstSelection.Function isa (InstSelection.Var isa) ->
  m (InstSelection.Function isa (Register isa))
allocRegistersFunction dict function = do
  blocks' <- traverse (allocRegistersBlock dict) function.blocks
  pure function{InstSelection.blocks = blocks'}