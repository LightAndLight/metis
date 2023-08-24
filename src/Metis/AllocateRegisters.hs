{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
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

import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (evalStateT)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Int (Int64)
import qualified Data.Maybe as Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import Data.Word (Word64)
import GHC.Stack (HasCallStack)
import qualified Metis.Anf as Anf
import Metis.Isa (Add, Instruction, Memory (..), Register, Sub, add, imm, mov, pop, push, sub)
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

data AllocateRegistersState isa = AllocateRegistersState
  { nextStackOffset :: Int64
  , available :: Seq (Register isa)
  , locations :: HashMap Anf.Var (Location isa)
  , liveness :: HashMap Anf.Var Liveness
  }

initialAllocateRegistersState ::
  Seq (Register isa) ->
  HashMap Anf.Var Liveness ->
  AllocateRegistersState isa
initialAllocateRegistersState available liveness =
  AllocateRegistersState
    { nextStackOffset = 0
    , available
    , locations = mempty
    , liveness
    }

lookupLocation :: (HasCallStack) => (MonadState (AllocateRegistersState isa) m) => Anf.Var -> m (Location isa)
lookupLocation var = gets (Maybe.fromMaybe (error $ show var <> "missing from location map") . HashMap.lookup var . (.locations))

lookupLiveness :: (HasCallStack) => (MonadState (AllocateRegistersState isa) m) => Anf.Var -> m Liveness
lookupLiveness var = gets (Maybe.fromMaybe (error $ show var <> "missing from liveness map") . HashMap.lookup var . (.liveness))

lookupSize :: (HasCallStack) => Anf.Var -> HashMap Anf.Var Word64 -> Word64
lookupSize var varSizes = Maybe.fromMaybe (error $ show var <> " missing from sizes map") $ HashMap.lookup var varSizes

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

allocateRegisters_X86_64 ::
  (MonadLog m) =>
  Seq (Register X86_64) ->
  Anf.Expr ->
  HashMap Anf.Var Liveness ->
  m ([Instruction X86_64], Location X86_64)
allocateRegisters_X86_64 available expr liveness =
  evalStateT
    (allocateRegistersExpr_X86_64 mempty expr)
    (initialAllocateRegistersState available liveness)

allocateRegistersLiteral_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  Literal ->
  m ([Instruction X86_64], Location X86_64)
allocateRegistersLiteral_X86_64 lit = do
  location <- allocLocation (Type.sizeOf $ Literal.typeOf lit)
  case location of
    Stack offset ->
      pure ([mov (imm lit) Mem{base = Rbp, offset}], location)
    Register register ->
      pure ([mov (imm lit) register], location)

allocateRegistersSimple_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  Anf.Simple ->
  m ([Instruction X86_64], Location X86_64)
allocateRegistersSimple_X86_64 simple =
  case simple of
    Anf.Var var -> do
      location <- lookupLocation var
      pure ([], location)
    Anf.Literal lit ->
      allocateRegistersLiteral_X86_64 lit

freeKills :: (MonadState (AllocateRegistersState isa) m) => Anf.Var -> m ()
freeKills var = do
  liveness <- lookupLiveness var
  modify
    ( \s ->
        let freed =
              HashMap.foldrWithKey'
                (\k v acc -> if k `HashSet.member` liveness.kills then v : acc else acc)
                []
                s.locations
         in s
              { available =
                  foldr
                    ( \location acc ->
                        case location of
                          Register register -> register Seq.<| acc
                          _ -> acc
                    )
                    s.available
                    freed
              }
    )

allocateRegistersExpr_X86_64 ::
  (MonadState (AllocateRegistersState X86_64) m, MonadLog m) =>
  HashMap Anf.Var Word64 ->
  Anf.Expr ->
  m ([Instruction X86_64], Location X86_64)
allocateRegistersExpr_X86_64 varSizes expr =
  case expr of
    Anf.Simple simple ->
      allocateRegistersSimple_X86_64 simple
    Anf.LetS var varInfo value rest -> do
      freeKills var

      value' <- do
        (insts, location) <- case value of
          Anf.Var var' -> do
            location <- lookupLocation var'
            pure ([], location)
          Anf.Literal lit -> do
            location <- allocLocation varInfo.size
            case location of
              Stack offset ->
                pure ([mov (imm lit) Mem{base = Rbp, offset}], location)
              Register register ->
                pure ([mov (imm lit) register], location)
        modify (\s -> s{locations = HashMap.insert var location s.locations})
        pure insts

      (rest', location) <- allocateRegistersExpr_X86_64 varSizes rest

      pure (value' <> rest', location)
    Anf.LetC var _varInfo value rest -> do
      value' <-
        case value of
          Anf.Binop op a b -> do
            Log.trace . Text.pack $ "LetC variable: " <> show var
            Log.trace . Text.pack $ "LetC value: " <> show value

            let op' :: (Add X86_64 a b, Sub X86_64 a b) => a -> b -> Instruction X86_64
                op' =
                  case op of
                    Anf.Add -> add
                    Anf.Subtract -> sub

            freeKills var

            (bInsts, bLocation) <-
              case b of
                Anf.Literal lit ->
                  allocateRegistersLiteral_X86_64 lit
                Anf.Var bVar -> do
                  liveness <- lookupLiveness var
                  bLocation <- lookupLocation bVar

                  insts <-
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
                    if bVar `HashSet.member` liveness.kills
                      then do
                        {- `var` "kills" `bVar`, which means `bVar` is not used after this instruction.

                        `bVar`'s location can be safely reused for `var`.
                        -}
                        Log.trace . Text.pack $ show bVar <> " in " <> show liveness.kills
                        pure []
                      else do
                        Log.trace . Text.pack $ show bVar <> " not in " <> show liveness.kills
                        {-
                        After this instruction, `bVar`'s location is "owned" by `var`.
                        `bVar` is used after this instruction, which means `bVar`'s location needs to
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
                        bLocation' <- allocLocation (lookupSize bVar varSizes)
                        modify (\s -> s{locations = HashMap.insert bVar bLocation' s.locations})
                        case (bLocation, bLocation') of
                          (Register bRegister, Register bRegister') ->
                            pure [mov bRegister bRegister']
                          (Register bRegister, Stack bOffset') ->
                            pure [mov bRegister Mem{base = Rbp, offset = bOffset'}]
                          (Stack bOffset, Register bRegister') ->
                            pure [mov Mem{base = Rbp, offset = bOffset} bRegister']
                          (Stack bOffset, Stack bOffset') ->
                            pure
                              [ push Rax
                              , mov Mem{base = Rbp, offset = bOffset} Rax
                              , mov Rax Mem{base = Rbp, offset = bOffset'}
                              , pop Rax
                              ]
                  pure (insts, bLocation)

            insts <-
              case a of
                Anf.Literal lit ->
                  case bLocation of
                    Stack bOffset ->
                      pure [op' (imm lit) Mem{base = Rbp, offset = bOffset}]
                    Register bRegister ->
                      pure [op' (imm lit) bRegister]
                Anf.Var aVar -> do
                  aLocation <- lookupLocation aVar
                  case (aLocation, bLocation) of
                    (Register aRegister, Register bRegister) ->
                      pure [op' aRegister bRegister]
                    (Register aRegister, Stack bOffset) ->
                      pure [op' aRegister Mem{base = Rbp, offset = bOffset}]
                    (Stack aOffset, Register bRegister) -> do
                      pure [op' Mem{base = Rbp, offset = aOffset} bRegister]
                    (Stack aOffset, Stack bOffset) ->
                      pure
                        [ push Rax
                        , mov Mem{base = Rbp, offset = aOffset} Rax
                        , op' Rax Mem{base = Rbp, offset = bOffset}
                        , pop Rax
                        ]

            modify (\s -> s{locations = HashMap.insert var bLocation s.locations})

            pure $ bInsts <> insts

      (rest', location) <- allocateRegistersExpr_X86_64 varSizes rest

      pure (value' <> rest', location)