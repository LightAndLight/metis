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
import Control.Lens.Fold ((^?))
import Control.Lens.Prism (Prism')
import Control.Lens.Review ((#))
import Control.Monad (when, (<=<))
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.Trans.Writer.CPS (runWriterT)
import Control.Monad.Writer.CPS (execWriterT)
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
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Stack (HasCallStack)
import qualified Metis.InstSelectionNew as InstSelection
import Metis.IsaNew (Address (..), AddressBase (..), Isa (..))
import Metis.LivenessNew (Liveness (..))
import Metis.Log (MonadLog)
import qualified Metis.Log as Log
import qualified Metis.SSA.Var as SSA
import Witherable (mapMaybe, wither)

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
  (HasCallStack) =>
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Register isa))) m
  , MonadLog m
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
            (error $ show var <> " missing from map: " <> show s.locations)
            (HashMap.lookup var s.locations)
      )
  case location of
    Spilled mem _ -> do
      reg <- allocateRegister dict uncons conflicts
      assignRegister var reg
      tell . DList.singleton $ load reg mem
      pure reg
    NotSpilled reg -> do
      Log.trace . Text.pack $ show var <> " is assigned to " <> show reg
      pure reg

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
  , MonadLog m
  ) =>
  SSA.Var ->
  Register isa ->
  m ()
assignRegister var reg = do
  Log.trace . Text.pack $ "assigning " <> show var <> " to " <> show reg
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
  { traverseVars :: forall var var' m. (Applicative m) => (var -> m var') -> Instruction isa var -> m (Instruction isa var')
  -- ^ A function that visits every variable in an instruction. Must visit variable "uses" before "defs".
  , instructionVarInfo :: forall var. Instruction isa var -> Instruction isa (VarInfo var)
  , load :: forall var. var -> Address var -> Instruction isa var
  , store :: forall var. Address var -> var -> Instruction isa var
  , move :: forall var. Prism' (Instruction isa var) (var, var)
  }

data VarInfo var
  = VarInfo (Usage var) var
  deriving (Eq, Show)

data Usage var
  = Use [var]
  | DefReuse var
  | DefNew
  deriving (Eq, Show)

selectRegister :: (Eq a) => a -> Seq a -> Maybe (a, Seq a)
selectRegister physical available = do
  index <- Seq.findIndexL (== physical) available
  let (prefix, suffix) = Seq.splitAt index available
  case Seq.viewl suffix of
    Seq.EmptyL ->
      Nothing
    register Seq.:< registers ->
      Just (register, prefix <> registers)

-- | Allocate a specific register for use, relocating its contents if they are still live.
forceAllocateRegister ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadWriter (DList (Instruction isa (Register isa))) m
  , MonadState (AllocRegistersState isa) m
  , MonadLog m
  ) =>
  AllocRegisters isa ->
  Register isa ->
  m ()
forceAllocateRegister dict@AllocRegisters{move, store} destRegister = do
  occupiedRegisters <- gets (.occupiedRegisters)
  case HashMap.lookup destRegister occupiedRegisters of
    Nothing -> do
      _ <- allocateRegister dict (selectRegister destRegister) []
      pure ()
    Just varToRelocate -> do
      hasFreeRegisters <- gets (not . null . (.freeRegisters))
      if hasFreeRegisters
        then do
          temp <- allocateRegister dict uncons []
          assignRegister varToRelocate temp
          tell . DList.singleton $ move # (temp, destRegister)
        else do
          let size = registerSize destRegister
          address <- allocateLocal size
          setSpilled varToRelocate address size
          tell . DList.singleton $ store address destRegister

allocRegistersVar ::
  forall isa m.
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadWriter (DList (Instruction isa (Register isa))) m
  , MonadLog m
  ) =>
  AllocRegisters isa ->
  VarInfo (InstSelection.Var isa) ->
  m (Register isa)
allocRegistersVar dict (VarInfo info var) =
  case var of
    InstSelection.Physical _mVirtual physical ->
      case info of
        Use conflicts -> do
          locations <- gets (.locations)
          when
            ( physical
                `elem` mapMaybe
                  ( \case
                      InstSelection.Physical _ p -> Just p
                      InstSelection.Virtual v -> do
                        location <- HashMap.lookup v locations
                        case location of
                          Spilled{} ->
                            Nothing
                          NotSpilled reg ->
                            pure reg
                  )
                  conflicts
            )
            (error "register conflict")

          pure physical
        DefNew -> do
          error "TODO: allocRegistersVar/Physical/DefNew"
        {-
        for_ mVirtual $ freeVars <=< getKilledBy

        occupiedRegisters <- gets (.occupiedRegisters)

        pure physical
        -}
        DefReuse src ->
          error "TODO: allocRegistersVar/Physical/DefReuse" src
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

allocRegistersInstruction ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadLog m
  ) =>
  AllocRegisters isa ->
  Instruction isa (InstSelection.Var isa) ->
  m [Instruction isa (Register isa)]
allocRegistersInstruction dict@AllocRegisters{traverseVars, instructionVarInfo, load, move} inst = do
  Log.trace . Text.pack $ "allocRegistersInstruction: " <> show inst

  case inst ^? move of
    Just (dest, src) ->
      case dest of
        InstSelection.Physical mDestVar destRegister -> do
          for_ mDestVar $ freeVars <=< getKilledBy

          case src of
            InstSelection.Physical _mSrcVar srcRegister ->
              if srcRegister == destRegister
                then pure []
                else do
                  insts <- fmap DList.toList . execWriterT $ forceAllocateRegister dict destRegister
                  pure $ insts <> [move # (destRegister, srcRegister)]
            InstSelection.Virtual srcVar -> do
              locations <- gets (.locations)
              case HashMap.lookup srcVar locations of
                Nothing ->
                  error $ show srcVar <> " missing from locations map"
                Just srcLocation ->
                  case srcLocation of
                    Spilled srcAddress _size -> do
                      insts <- fmap DList.toList . execWriterT $ forceAllocateRegister dict destRegister
                      pure $ insts <> [load destRegister srcAddress]
                    NotSpilled srcRegister ->
                      if srcRegister == destRegister
                        then pure []
                        else do
                          insts <- fmap DList.toList . execWriterT $ forceAllocateRegister dict destRegister
                          pure $ insts <> [move # (destRegister, srcRegister)]
        InstSelection.Virtual destVar -> do
          freeVars =<< getKilledBy destVar

          locations <- gets (.locations)
          case HashMap.lookup destVar locations of
            Nothing ->
              pure ()
            Just location ->
              error $ "the `move` destination " <> show destVar <> " already has a location: " <> show location

          case src of
            InstSelection.Physical _mVar register -> do
              assignRegister destVar register
              pure []
            InstSelection.Virtual srcVar ->
              case HashMap.lookup destVar locations of
                Nothing ->
                  error $ show srcVar <> " missing from locations map"
                Just srcLocation -> do
                  modify (\s -> s{locations = HashMap.insert destVar srcLocation s.locations})
                  pure []
    Nothing -> do
      (lastInst, insts) <-
        runWriterT
          . traverseVars (allocRegistersVar dict)
          $ instructionVarInfo inst
      pure . DList.toList $ insts <> DList.singleton lastInst

allocRegisters ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadLog m
  ) =>
  AllocRegisters isa ->
  [Instruction isa (InstSelection.Var isa)] ->
  m [Instruction isa (Register isa)]
allocRegisters dict =
  fmap concat . traverse (allocRegistersInstruction dict)

allocRegistersBlock ::
  ( Isa isa
  , MonadReader AllocRegistersEnv m
  , MonadState (AllocRegistersState isa) m
  , MonadLog m
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
  , MonadLog m
  ) =>
  AllocRegisters isa ->
  InstSelection.Function isa (InstSelection.Var isa) ->
  m (InstSelection.Function isa (Register isa))
allocRegistersFunction dict function = do
  blocks' <- traverse (allocRegistersBlock dict) function.blocks
  pure function{InstSelection.blocks = blocks'}