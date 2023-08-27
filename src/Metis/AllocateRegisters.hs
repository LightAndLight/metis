{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Metis.AllocateRegisters (
  allocateRegisters_X86_64,

  -- * Internals
  Location (..),
  AllocateRegistersState (..),
  initialAllocateRegistersState,
  allocateRegistersExpr_X86_64,
  -- allocateRegistersCompound_X86_64,
) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (runReaderT)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (runStateT)
import Data.Foldable (traverse_)
import qualified Data.HashMap.Lazy as HashMap.Lazy
import qualified Data.HashMap.Lazy as Lazy (HashMap)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Int (Int64)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Stack (HasCallStack)
import qualified Metis.Anf as Anf
import Metis.Asm (Block (..), BlockAttribute)
import Metis.Asm.Class (MonadAsm)
import qualified Metis.Asm.Class as Asm
import Metis.Isa (
  Add,
  Instruction,
  Memory (..),
  Op2 (..),
  Register,
  Sub,
  Symbol (..),
  add,
  cmp,
  imm,
  je,
  jmp,
  mov,
  pop,
  push,
  sub,
 )
import Metis.Isa.X86_64 (Register (..), X86_64)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.Liveness (Liveness (..))
import Metis.Log (MonadLog)
import qualified Metis.Log as Log
import qualified Metis.Type as Type

data Location isa
  = Register (Register isa)
  | Stack {offset :: Int64}

deriving instance (Show (Register isa)) => Show (Location isa)
deriving instance (Eq (Register isa)) => Eq (Location isa)

data AllocateRegistersState isa = AllocateRegistersState
  { nextStackOffset :: Int64
  , available :: Seq (Register isa)
  , locations :: Lazy.HashMap Anf.Var (Location isa)
  , labelArgLocations :: HashMap Anf.Var (Location isa)
  , liveness :: HashMap Anf.Var Liveness
  , previousBlocks :: [Block isa]
  , currentBlockName :: Text
  , currentBlockAttributes :: [BlockAttribute]
  , currentBlockInstructions :: [Instruction isa]
  }

initialAllocateRegistersState ::
  Seq (Register isa) ->
  HashMap Anf.Var Liveness ->
  Text ->
  [BlockAttribute] ->
  AllocateRegistersState isa
initialAllocateRegistersState available liveness blockName blockAttributes =
  AllocateRegistersState
    { nextStackOffset = 0
    , available
    , locations = mempty
    , labelArgLocations = mempty
    , liveness
    , previousBlocks = []
    , currentBlockName = blockName
    , currentBlockAttributes = blockAttributes
    , currentBlockInstructions = []
    }

lookupLocation :: (HasCallStack) => (MonadState (AllocateRegistersState isa) m) => Anf.Var -> m (Location isa)
lookupLocation var = gets (Maybe.fromMaybe (error $ show var <> "missing from location map") . HashMap.Lazy.lookup var . (.locations))

lookupLiveness :: (HasCallStack) => (MonadState (AllocateRegistersState isa) m) => Anf.Var -> m Liveness
lookupLiveness var = gets (Maybe.fromMaybe (error $ show var <> "missing from liveness map") . HashMap.lookup var . (.liveness))

lookupSize :: (HasCallStack) => Anf.Var -> HashMap Anf.Var Word64 -> Word64
lookupSize var varSizes = Maybe.fromMaybe (error $ show var <> " missing from sizes map") $ HashMap.lookup var varSizes

data AllocateRegistersEnv isa = AllocateRegistersEnv
  { labelArgs :: Anf.Var -> Anf.Var
  , labelArgLocations :: Lazy.HashMap Anf.Var (Location isa)
  }

lookupLabelArgLocation :: (HasCallStack) => (MonadReader (AllocateRegistersEnv isa) m) => Anf.Var -> m (Location isa)
lookupLabelArgLocation var = asks (Maybe.fromMaybe (error $ show var <> "missing from label arg location map") . HashMap.Lazy.lookup var . (.labelArgLocations))

lookupLabelArg :: (HasCallStack) => (MonadReader (AllocateRegistersEnv isa) m) => Anf.Var -> m Anf.Var
lookupLabelArg var = do
  f <- asks (.labelArgs)
  pure $ f var

emit ::
  (MonadState (AllocateRegistersState isa) m) =>
  [Instruction isa] ->
  m ()
emit instructions =
  modify (\s -> s{currentBlockInstructions = s.currentBlockInstructions <> instructions})

declareLabel ::
  (MonadState (AllocateRegistersState isa) m) =>
  Text ->
  m (Symbol, m ())
declareLabel value = do
  pure
    ( Symbol value
    , modify
        ( \s ->
            s
              { previousBlocks =
                  s.previousBlocks
                    <> [ Block
                          { label = s.currentBlockName
                          , attributes = s.currentBlockAttributes
                          , instructions = s.currentBlockInstructions
                          }
                       ]
              , currentBlockName = value
              , currentBlockInstructions = []
              }
        )
    )

beginBlock ::
  (MonadState (AllocateRegistersState isa) m) =>
  Text ->
  m Symbol
beginBlock label =
  Symbol label
    <$ modify
      ( \s ->
          s
            { previousBlocks =
                s.previousBlocks
                  <> [ Block
                        { label = s.currentBlockName
                        , attributes = s.currentBlockAttributes
                        , instructions = s.currentBlockInstructions
                        }
                     ]
            , currentBlockName = label
            , currentBlockInstructions = []
            }
      )

allocLocation ::
  (MonadState (AllocateRegistersState isa) m) =>
  Word64 ->
  m (Location isa)
allocLocation size = do
  available <- gets (.available)
  case Seq.viewl available of
    Seq.EmptyL -> do
      offset <- gets (.nextStackOffset)
      let location = Stack offset
      modify (\s -> s{nextStackOffset = offset - fromIntegral @Word64 @Int64 size})
      pure location
    register Seq.:< available' -> do
      modify (\s -> s{available = available'})
      pure $ Register register

freeLocation ::
  (MonadState (AllocateRegistersState isa) m) =>
  Location isa ->
  m ()
freeLocation location =
  case location of
    Register register ->
      modify (\s -> s{available = register Seq.<| s.available})
    Stack{} ->
      pure ()

allocateRegisters_X86_64 ::
  (MonadAsm X86_64 m, MonadLog m, MonadFix m) =>
  Seq (Register X86_64) ->
  Anf.ExprInfo ->
  Anf.Expr ->
  HashMap Anf.Var Liveness ->
  Text ->
  [BlockAttribute] ->
  m (Location X86_64)
allocateRegisters_X86_64 available exprInfo expr liveness blockName blockAttributes = do
  rec (a, s) <-
        runStateT
          ( runReaderT
              (allocateRegistersExpr_X86_64 mempty expr)
              AllocateRegistersEnv
                { labelArgs = exprInfo.labelArgs
                , labelArgLocations = s.labelArgLocations
                }
          )
          (initialAllocateRegistersState available liveness blockName blockAttributes)
  traverse_ (\Block{label, attributes, instructions} -> Asm.block label attributes instructions) s.previousBlocks
  _ <- Asm.block s.currentBlockName s.currentBlockAttributes s.currentBlockInstructions
  pure a

allocateRegistersLiteral_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  Literal ->
  m (Location X86_64)
allocateRegistersLiteral_X86_64 lit = do
  location <- allocLocation (Type.sizeOf $ Literal.typeOf lit)
  case location of
    Stack offset -> do
      emit [mov Op2{src = imm lit, dest = Mem{base = Rbp, offset}}]
      pure location
    Register register -> do
      emit [mov Op2{src = imm lit, dest = register}]
      pure location

allocateRegistersSimple_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  Anf.Simple ->
  m (Location X86_64)
allocateRegistersSimple_X86_64 simple =
  case simple of
    Anf.Var var ->
      lookupLocation var
    Anf.Literal lit ->
      allocateRegistersLiteral_X86_64 lit

freeKills :: (MonadState (AllocateRegistersState isa) m, MonadLog m) => Anf.Var -> m ()
freeKills var = do
  liveness <- lookupLiveness var
  Log.trace . Text.pack $ show var <> " kills " <> show liveness.kills

  modify
    ( \s ->
        let freed =
              HashMap.Lazy.foldrWithKey'
                (\k v acc -> if k `HashSet.member` liveness.kills then v : acc else acc)
                []
                s.locations
            available =
              foldr
                ( \location acc ->
                    case location of
                      Register register -> register Seq.<| acc
                      _ -> acc
                )
                s.available
                freed
         in s{available}
    )

allocateRegistersExpr_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadReader (AllocateRegistersEnv X86_64) m, MonadLog m) =>
  HashMap Anf.Var Word64 ->
  Anf.Expr ->
  m (Location X86_64)
allocateRegistersExpr_X86_64 varSizes expr =
  case expr of
    Anf.Return simple ->
      allocateRegistersSimple_X86_64 simple
    Anf.LetS var varInfo value rest -> do
      freeKills var

      valueLocation <-
        case value of
          Anf.Var var' ->
            lookupLocation var'
          Anf.Literal lit -> do
            location <- allocLocation varInfo.size
            case location of
              Stack offset -> do
                emit [mov Op2{src = imm lit, dest = Mem{base = Rbp, offset}}]
                pure location
              Register register -> do
                emit [mov Op2{src = imm lit, dest = register}]
                pure location
      modify (\s -> s{locations = HashMap.Lazy.insert var valueLocation s.locations})

      allocateRegistersExpr_X86_64 varSizes rest
    Anf.LetC var _varInfo value rest -> do
      Log.trace "LetC"
      Log.trace . Text.pack $ "  var: " <> show var
      Log.trace . Text.pack $ "  value: " <> show value

      freeKills var

      case value of
        Anf.Binop op a b -> do
          let op' :: (Add X86_64 a b, Sub X86_64 a b) => Op2 a b -> Instruction X86_64
              op' =
                case op of
                  Anf.Add -> add
                  Anf.Subtract -> sub

          -- Binop convention: the first argument is the "destination". Motivated by subtraction
          -- in assembly, which is `dest := dest - src`.
          aLocation <-
            case a of
              Anf.Literal lit ->
                allocateRegistersLiteral_X86_64 lit
              Anf.Var aVar -> do
                liveness <- lookupLiveness var
                aLocation <- lookupLocation aVar

                {- x86-64 2-operand instructions such as `add` and `sub` store their result in
                their second operand (assuming AT&T syntax).

                Thus for an A-normal form instruction like `%1 = add(%2, %3)`, `%1` and `%3`
                need to be assigned the same location. The fast path is when `%1` kills `%3`:
                after the instruction `%3` is no longer relevant, so `%1` can steal `%3`'s
                location.

                When `%1` *doesn't* kill `%3`, we have to assign a fresh location to `%1` and
                move the contents of `%3` to this location before executing the instruction.
                `%3` is still relevant later on so we have to preserve its value.
                -}
                if aVar `HashSet.member` liveness.kills
                  then do
                    {- `var` "kills" `aVar`, which means `aVar` is not used after this instruction.

                    `aVar`'s location can be safely reused for `var`.
                    -}
                    Log.trace . Text.pack $ show aVar <> " in " <> show liveness.kills
                  else do
                    Log.trace . Text.pack $ show aVar <> " not in " <> show liveness.kills
                    {-
                    After this instruction, `aVar`'s location is "owned" by `var`.
                    `aVar` is used after this instruction, which means `aVar`'s location needs to
                    be preserved.

                    Example:

                    (2 + 1) + ((2 + 1) + 1)
                    = 3 + 3 + 1
                    = 7

                    ```
                    %0 = 1
                    %1 = add(2, %0)
                    %2 = add(%1, %0)
                    ```

                    Incorrect assignment:

                    (2 + 1) + ((2 + 1) + (2 + 1))
                    = 3 + 3 + 3
                    = 9

                    ```
                    mov $1, %rax
                    add $2, %rax
                    add %rax, %rax
                    ```

                    Correct assignment:

                    (2 + 1) + ((2 + 1) + 1)
                    = 3 + 3 + 1
                    = 7

                    ```
                    mov $1, %rax
                    mov %rax, %rbx
                    add $2, %rax
                    add %rax, %rbx
                    ```
                    -}
                    aLocation' <- allocLocation (lookupSize aVar varSizes)
                    modify (\s -> s{locations = HashMap.Lazy.insert aVar aLocation' s.locations})
                    case (aLocation, aLocation') of
                      (Register aRegister, Register aRegister') ->
                        emit [mov Op2{src = aRegister, dest = aRegister'}]
                      (Register aRegister, Stack aOffset') ->
                        emit [mov Op2{src = aRegister, dest = Mem{base = Rbp, offset = aOffset'}}]
                      (Stack aOffset, Register aRegister') ->
                        emit [mov Op2{src = Mem{base = Rbp, offset = aOffset}, dest = aRegister'}]
                      (Stack aOffset, Stack aOffset') ->
                        emit
                          [ push Rax
                          , mov Op2{src = Mem{base = Rbp, offset = aOffset}, dest = Rax}
                          , mov Op2{src = Rax, dest = Mem{base = Rbp, offset = aOffset'}}
                          , pop Rax
                          ]
                pure aLocation

          case b of
            Anf.Literal lit -> do
              case aLocation of
                Stack bOffset ->
                  emit [op' Op2{src = imm lit, dest = Mem{base = Rbp, offset = bOffset}}]
                Register bRegister ->
                  emit [op' Op2{src = imm lit, dest = bRegister}]
            Anf.Var bVar -> do
              bLocation <- lookupLocation bVar
              emit $ case (aLocation, bLocation) of
                (Register aRegister, Register bRegister) ->
                  [op' Op2{dest = aRegister, src = bRegister}]
                (Register aRegister, Stack bOffset) ->
                  [op' Op2{dest = aRegister, src = Mem{base = Rbp, offset = bOffset}}]
                (Stack aOffset, Register bRegister) -> do
                  [op' Op2{dest = Mem{base = Rbp, offset = aOffset}, src = bRegister}]
                (Stack aOffset, Stack bOffset) ->
                  [ push Rax
                  , mov Op2{src = Mem{base = Rbp, offset = bOffset}, dest = Rax}
                  , op' Op2{dest = Mem{base = Rbp, offset = aOffset}, src = Rax}
                  , pop Rax
                  ]

          modify (\s -> s{locations = HashMap.Lazy.insert var aLocation s.locations})

      allocateRegistersExpr_X86_64 varSizes rest
    Anf.IfThenElse cond then_ else_ rest -> do
      condLocation <-
        case cond of
          Anf.Var var ->
            lookupLocation var
          Anf.Literal lit ->
            allocateRegistersLiteral_X86_64 lit
      case condLocation of
        Register register ->
          emit [cmp register (imm @Word64 0)]
        Stack offset ->
          emit [cmp Mem{base = Rbp, offset} (imm @Word64 0)]
      case cond of
        Anf.Var{} -> pure ()
        Anf.Literal{} ->
          freeLocation condLocation

      (_thenLabel, beginThen) <- declareLabel "then"
      (elseLabel, beginElse) <- declareLabel "else"
      emit [je elseLabel]

      available <- gets (.available)

      beginThen
      _ <- allocateRegistersExpr_X86_64 varSizes then_
      modify (\s -> s{available})

      beginElse
      _ <- allocateRegistersExpr_X86_64 varSizes else_
      modify (\s -> s{available})

      allocateRegistersExpr_X86_64 varSizes rest
    Anf.Jump label arg -> do
      Log.trace "jump"
      Log.trace . Text.pack $ "  label: " <> show label
      Log.trace . Text.pack $ "  arg: " <> show arg

      labelArg <- lookupLabelArg label
      freeKills labelArg

      argLocation <- allocateRegistersSimple_X86_64 arg
      labelArgLocation <- lookupLabelArgLocation label
      emit $
        -- If we're jumping forward to a label then `labelArgLocation` isn't known yet. It will be
        -- computed when we examine the corresponding block. Therefore we can't `emit` based on
        -- the value of `labelArgLocation`. The inspection of `labelArgLocation` has to be delayed
        -- until after we've examined the whole expression.
        if argLocation == labelArgLocation
          then []
          else case (argLocation, labelArgLocation) of
            (Register argRegister, Register labelArgRegister) ->
              [mov Op2{src = argRegister, dest = labelArgRegister}]
            (Register argRegister, Stack labelArgOffset) ->
              [mov Op2{src = argRegister, dest = Mem{base = Rbp, offset = labelArgOffset}}]
            (Stack argOffset, Register labelArgRegister) -> do
              [mov Op2{src = Mem{base = Rbp, offset = argOffset}, dest = labelArgRegister}]
            (Stack argOffset, Stack labelArgOffset) ->
              [ push Rax
              , mov Op2{src = Mem{base = Rbp, offset = argOffset}, dest = Rax}
              , mov Op2{src = Rax, dest = Mem{base = Rbp, offset = labelArgOffset}}
              , pop Rax
              ]

      emit [jmp $ Symbol . Text.pack $ "block_" <> show label.value]
      pure undefined -- TODO: How do I remove this undefined? Some tweak to the ANF representation?
    Anf.Label label arg rest -> do
      Log.trace "block"
      Log.trace . Text.pack $ "  label: " <> show label
      Log.trace . Text.pack $ "  arg: " <> show arg

      _ <- beginBlock . Text.pack $ "block_" <> show label.value
      argLocation <- allocLocation $ lookupSize arg varSizes
      modify
        ( \s ->
            s
              { locations = HashMap.Lazy.insert arg argLocation s.locations
              , labelArgLocations = HashMap.Lazy.insert label argLocation s.labelArgLocations
              }
        )

      allocateRegistersExpr_X86_64 varSizes rest