{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Metis.InstSelection (
  instSelection_X86_64,

  -- * Internals
  Location (..),
  InstSelectionState (..),
  initialInstSelectionState,
  instSelectionExpr_X86_64,
  RegisterFunctionArgument (..),
  moveRegisterFunctionArguments,
) where

import Control.Monad (when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (runReaderT)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (runStateT)
import Data.Foldable (foldl', for_, traverse_)
import qualified Data.HashMap.Lazy as HashMap.Lazy
import qualified Data.HashMap.Lazy as Lazy (HashMap)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
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
  Isa (generalPurposeRegisters),
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
import Metis.Type (Type)
import qualified Metis.Type as Type

data Location isa
  = Register (Register isa)
  | Stack {offset :: Int64}

deriving instance (Show (Register isa)) => Show (Location isa)
deriving instance (Eq (Register isa)) => Eq (Location isa)

data InstSelectionState isa = InstSelectionState
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

initialInstSelectionState ::
  Seq (Register isa) ->
  HashMap Anf.Var Liveness ->
  Text ->
  [BlockAttribute] ->
  InstSelectionState isa
initialInstSelectionState available liveness blockName blockAttributes =
  InstSelectionState
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

lookupLocation :: (HasCallStack) => (MonadState (InstSelectionState isa) m) => Anf.Var -> m (Location isa)
lookupLocation var = gets (Maybe.fromMaybe (error $ show var <> " missing from location map") . HashMap.Lazy.lookup var . (.locations))

lookupLiveness :: (HasCallStack) => (MonadState (InstSelectionState isa) m) => Anf.Var -> m Liveness
lookupLiveness var = gets (Maybe.fromMaybe (error $ show var <> " missing from liveness map") . HashMap.lookup var . (.liveness))

lookupSize :: (HasCallStack) => Anf.Var -> HashMap Anf.Var Word64 -> Word64
lookupSize var varSizes = Maybe.fromMaybe (error $ show var <> "  missing from sizes map") $ HashMap.lookup var varSizes

data InstSelectionEnv isa = InstSelectionEnv
  { labelArgs :: Anf.Var -> Anf.Var
  , labelArgLocations :: Lazy.HashMap Anf.Var (Location isa)
  , nameTys :: Text -> Type
  , varTys :: Anf.Var -> Type
  }

lookupLabelArgLocation :: (HasCallStack) => (MonadReader (InstSelectionEnv isa) m) => Anf.Var -> m (Location isa)
lookupLabelArgLocation var = asks (Maybe.fromMaybe (error $ show var <> "missing from label arg location map") . HashMap.Lazy.lookup var . (.labelArgLocations))

lookupLabelArg :: (HasCallStack) => (MonadReader (InstSelectionEnv isa) m) => Anf.Var -> m Anf.Var
lookupLabelArg var = do
  f <- asks (.labelArgs)
  pure $ f var

emit ::
  (MonadState (InstSelectionState isa) m) =>
  [Instruction isa] ->
  m ()
emit instructions =
  modify (\s -> s{currentBlockInstructions = s.currentBlockInstructions <> instructions})

declareLabel ::
  (MonadState (InstSelectionState isa) m) =>
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
  (MonadState (InstSelectionState isa) m) =>
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
  (MonadState (InstSelectionState isa) m) =>
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
  (MonadState (InstSelectionState isa) m) =>
  Location isa ->
  m ()
freeLocation location =
  case location of
    Register register ->
      modify (\s -> s{available = register Seq.<| s.available})
    Stack{} ->
      pure ()

instSelection_X86_64 ::
  (MonadAsm X86_64 m, MonadLog m, MonadFix m) =>
  (Text -> Type) ->
  Seq (Register X86_64) ->
  Anf.ExprInfo ->
  Anf.Expr ->
  HashMap Anf.Var Liveness ->
  Text ->
  [BlockAttribute] ->
  m (Location X86_64)
instSelection_X86_64 nameTys available exprInfo expr liveness blockName blockAttributes = do
  rec (a, s) <-
        runStateT
          ( runReaderT
              (instSelectionExpr_X86_64 mempty expr)
              InstSelectionEnv
                { labelArgs = exprInfo.labelArgs
                , labelArgLocations = s.labelArgLocations
                , nameTys
                , varTys = exprInfo.varTys
                }
          )
          (initialInstSelectionState available liveness blockName blockAttributes)
  traverse_ (\Block{label, attributes, instructions} -> Asm.block label attributes instructions) s.previousBlocks
  _ <- Asm.block s.currentBlockName s.currentBlockAttributes s.currentBlockInstructions
  pure a

instSelectionLiteral_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadLog m) =>
  Literal ->
  m (Location X86_64)
instSelectionLiteral_X86_64 lit = do
  location <- allocLocation (Type.sizeOf $ Literal.typeOf lit)
  case location of
    Stack offset -> do
      emit [mov Op2{src = imm lit, dest = Mem{base = Rbp, offset}}]
      pure location
    Register register -> do
      emit [mov Op2{src = imm lit, dest = register}]
      pure location

instSelectionSimple_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadLog m) =>
  Anf.Simple ->
  m (Location X86_64)
instSelectionSimple_X86_64 simple =
  case simple of
    Anf.Var var ->
      lookupLocation var
    Anf.Literal lit ->
      instSelectionLiteral_X86_64 lit
    Anf.Name name ->
      error "TODO: instSelectionSimple_X86_64/Name" name

freeKills :: (MonadState (InstSelectionState isa) m, MonadLog m) => Anf.Var -> m ()
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

data FunctionArguments isa = FunctionArguments
  { registerFunctionArguments :: [RegisterFunctionArgument isa]
  -- ^ Arguments that will be passed via register.
  , stackFunctionArguments :: [StackFunctionArgument isa]
  -- ^ Arguments that will be passed via stack.
  }

instance Semigroup (FunctionArguments isa) where
  (<>) a b =
    FunctionArguments
      { registerFunctionArguments = a.registerFunctionArguments <> b.registerFunctionArguments
      , stackFunctionArguments = a.stackFunctionArguments <> b.stackFunctionArguments
      }

instance Monoid (FunctionArguments isa) where
  mempty =
    FunctionArguments
      { registerFunctionArguments = mempty
      , stackFunctionArguments = mempty
      }

data RegisterFunctionArgument isa = RegisterFunctionArgument
  { callerSave :: Bool
  -- ^ The caller needs to save the register when the register's current contents are used after the
  -- call returns.
  , size :: Word64
  , src :: Location isa
  , dest :: Register isa
  }

data StackFunctionArgument isa = StackFunctionArgument
  { src :: Location isa
  , dest :: Memory isa
  }

{-
stack argument 3         (16 + size_of(stack argument 1) + size_of(stack argument 2))(%rbp)
stack argument 2         (16 + size_of(stack argument 1))(%rbp)
stack argument 1         16(%rbp)
return address           8(%rbp)
caller's base pointer    0(%rbp)
local 1                  (-size_of(local 1))(%rbp)
local 2                  (-size_of(local 1) - size_of(local 2))(%rbp)
-}
setupFunctionArguments ::
  Seq (Register X86_64) ->
  HashSet (Register X86_64) ->
  Seq (Register X86_64) ->
  [Type] ->
  [Location X86_64] ->
  FunctionArguments X86_64
setupFunctionArguments registersAvailableAtCall registersKilledByCall availableArgumentRegisters argTys argLocations =
  case Seq.viewl availableArgumentRegisters of
    register Seq.:< availableArgumentRegisters' ->
      case (argTys, argLocations) of
        ([], []) ->
          mempty
        (argTy : argTys', argLocation : argLocations') ->
          ( case Type.callingConventionOf argTy of
              Type.Register ->
                FunctionArguments
                  { registerFunctionArguments =
                      [ RegisterFunctionArgument
                          { callerSave =
                              argLocation /= Register register
                                && register `notElem` registersAvailableAtCall
                                && not (register `HashSet.member` registersKilledByCall)
                          , size = Type.sizeOf argTy
                          , src = argLocation
                          , dest = register
                          }
                      ]
                  , stackFunctionArguments = []
                  }
              Type.Composite{} -> error "TODO: types with composite calling conventions"
          )
            <> setupFunctionArguments
              registersAvailableAtCall
              registersKilledByCall
              availableArgumentRegisters'
              argTys'
              argLocations'
        _ ->
          error $
            "argument types and argument locations have different number of elements: "
              <> show argTys
              <> ", "
              <> show argLocations
    Seq.EmptyL ->
      setupStackFunctionArguments
        -- Assumes that 0(%rbp) in the callee's stack frame contains the caller's frame pointer, and 8(%rbp)
        -- contains the return address.
        (2 * fromIntegral @Word64 @Int64 Type.pointerSize)
        argTys
        argLocations

{-
The function arguments require all available registers, so the remaining arguments must be passed
on the stack.
-}
setupStackFunctionArguments ::
  Int64 ->
  [Type] ->
  [Location X86_64] ->
  FunctionArguments X86_64
setupStackFunctionArguments offset argTys argLocations =
  case (argTys, argLocations) of
    ([], []) ->
      mempty
    (argTy : argTys', argLocation : argLocations') ->
      ( case Type.callingConventionOf argTy of
          Type.Register ->
            FunctionArguments
              { registerFunctionArguments = []
              , stackFunctionArguments = [StackFunctionArgument{src = argLocation, dest = Mem{base = Rbp, offset}}]
              }
          Type.Composite{} -> error "TODO: types with composite calling conventions"
      )
        <> setupStackFunctionArguments
          (offset + fromIntegral @Word64 @Int64 (Type.sizeOf argTy))
          argTys'
          argLocations'
    _ ->
      error $
        "argument types and argument locations have different number of elements: "
          <> show argTys
          <> ", "
          <> show argLocations

{-
Problem:

What if there's a caller-saved register argument that also needs to go into a stack
argument?

```
%c = f(%a, %b, %a)
```

Assuming we start with `%a -> %rbx` and `%b -> %rcx`, and only have `{%rax, %rbx}` as
argument-passing registers, we get:

```
mov %rbx, %rax
mov %rcx, %rbx // wrong! %rbx is overwritten too early.
push %rbx
push $after
push %rbp
mov %rsp, %rbp
jump $f
after:
...
```

Perhaps the problem is in using `%a` twice. What about:

```
%a_1, %a_2 = dup(%a)
%c = f(%a_1, %b, %a_2)
```

We can still start with `%a -> %rbx` and `%b -> %rcx`, then `%a_1, a_2 = clone(%a)` gives
`%a_1 -> %rbx` and `%a_2 -> dest` where `dest \notin {%rbx, %rcx}`.

```
mov %rbx, %rax
mov %rcx, %rbx
push dest
push $after
push %rbp
mov %rsp, %rbp
jump $f
after:
...
```

Another situation: `f(%b, %a)`. Assume `%a -> %rax` and `%b -> %rbx`, with no
stack-passed arguments.

```
mov %rbx, %rax
mov %rax, %rbx // wrong!
push $after
push %rbp
mov %rsp, %rbp
jump $f
after:
...
```

The general issue is "simultaneous reassignment of registers": how to tomically permute the values
in a particular set of registers.
-}
moveRegisterFunctionArguments ::
  (MonadState (InstSelectionState X86_64) m) =>
  HashMap (Register X86_64) (Location X86_64) ->
  [RegisterFunctionArgument X86_64] ->
  m [Instruction X86_64]
moveRegisterFunctionArguments registerRemapping arguments =
  case arguments of
    [] ->
      pure []
    [RegisterFunctionArgument{callerSave, size = _, src, dest}] -> do
      let pushDest = [push dest | callerSave]

      b <-
        case src of
          Register srcRegister ->
            case HashMap.lookup srcRegister registerRemapping of
              Nothing ->
                pure [mov Op2{src = srcRegister, dest} | srcRegister /= dest]
              Just srcRegisterRemapped -> do
                let a =
                      [ case srcRegisterRemapped of
                        Register srcRegisterRemappedRegister ->
                          mov Op2{src = srcRegisterRemappedRegister, dest}
                        Stack srcRegisterRemappedOffset ->
                          mov Op2{src = Mem{base = Rbp, offset = srcRegisterRemappedOffset}, dest}
                      | srcRegisterRemapped /= Register dest
                      ]
                freeLocation srcRegisterRemapped
                pure a
          Stack srcOffset ->
            pure [mov Op2{src = Mem{base = Rbp, offset = srcOffset}, dest}]

      pure $ pushDest <> b
    RegisterFunctionArgument{callerSave, size, src, dest} : arguments' -> do
      let pushDest = [push dest | callerSave]

      temp <- allocLocation size
      a <-
        case src of
          Register srcRegister ->
            case HashMap.lookup srcRegister registerRemapping of
              Nothing ->
                pure $
                  if srcRegister == dest
                    then []
                    else
                      saveDestination temp dest
                        <> [mov Op2{src = srcRegister, dest}]
              Just srcRegisterRemapped -> do
                let a =
                      if srcRegisterRemapped == Register dest
                        then []
                        else
                          saveDestination temp dest
                            <> [ case srcRegisterRemapped of
                                  Register srcRegisterRemappedRegister ->
                                    mov Op2{src = srcRegisterRemappedRegister, dest}
                                  Stack srcRegisterRemappedOffset ->
                                    mov Op2{src = Mem{base = Rbp, offset = srcRegisterRemappedOffset}, dest}
                               ]
                freeLocation srcRegisterRemapped
                pure a
          Stack srcOffset ->
            pure $ saveDestination temp dest <> [mov Op2{src = Mem{base = Rbp, offset = srcOffset}, dest}]

      b <- moveRegisterFunctionArguments (HashMap.insert dest temp registerRemapping) arguments'

      pure $ pushDest <> a <> b
  where
    saveDestination temp dest =
      [ case temp of
          Register tempRegister ->
            mov Op2{src = dest, dest = tempRegister}
          Stack tempOffset ->
            mov Op2{src = dest, dest = Mem{base = Rbp, offset = tempOffset}}
      ]

instSelectionExpr_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  HashMap Anf.Var Word64 ->
  Anf.Expr ->
  m (Location X86_64)
instSelectionExpr_X86_64 varSizes expr =
  case expr of
    Anf.Return simple ->
      instSelectionSimple_X86_64 simple
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
          Anf.Name name ->
            error "TODO: instSelectionExpr_X86_64/Name" name
      modify (\s -> s{locations = HashMap.Lazy.insert var valueLocation s.locations})

      instSelectionExpr_X86_64 varSizes rest
    Anf.LetC var _varInfo value rest -> do
      Log.trace "LetC"
      Log.trace . Text.pack $ "  var: " <> show var
      Log.trace . Text.pack $ "  value: " <> show value

      freeKills var

      case value of
        Anf.Call function args -> do
          functionLocation <- instSelectionSimple_X86_64 function
          argLocations <- traverse instSelectionSimple_X86_64 args

          nameTys <- asks (.nameTys)
          varTys <- asks (.varTys)
          case Anf.typeOf nameTys varTys function of
            Type.Fn argTys _retTy -> do
              registersAvailableAtCall <- gets (.available)
              registersKilledByCall <- do
                varLiveness <- lookupLiveness var
                foldl'
                  ( \acc location -> case location of
                      Register register -> HashSet.insert register acc
                      Stack{} -> acc
                  )
                  mempty
                  <$> traverse lookupLocation (HashSet.toList varLiveness.kills)

              let functionArguments =
                    setupFunctionArguments
                      registersAvailableAtCall
                      registersKilledByCall
                      (generalPurposeRegisters @X86_64)
                      argTys
                      argLocations

              emit =<< moveRegisterFunctionArguments mempty functionArguments.registerFunctionArguments

              for_ (reverse functionArguments.stackFunctionArguments) $ \StackFunctionArgument{src, dest = _} -> do
                emit
                  [ case src of
                      Register register -> push register
                      Stack offset -> push Mem{base = Rbp, offset}
                  ]

              (label, emitLabel) <- declareLabel "after"
              emit [push (imm label)]

              emit [push Rbp, mov Op2{src = Rsp, dest = Rbp}]

              emit
                [ case functionLocation of
                    Register register ->
                      jmp register
                    Stack offset ->
                      jmp Mem{base = Rbp, offset}
                ]

              emitLabel
              {-
              %rbp popped by callee
              return address popeed by callee
              stack function arguments popped by callee
              -}
              for_ (reverse functionArguments.registerFunctionArguments) $ \RegisterFunctionArgument{callerSave, src = _, dest} -> do
                when callerSave $ emit [pop dest]

              pure (error "TODO: call instruction")
            ty -> error $ "trying to call a non-function type: " <> show ty
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
              Anf.Name name ->
                error "TODO: instSelectionExpr_X86_64/Binop/a/Name" name
              Anf.Literal lit ->
                instSelectionLiteral_X86_64 lit
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
            Anf.Name name ->
              error "TODO: instSelectionExpr_X86_64/Binop/b/Name" name
            Anf.Literal lit -> do
              case aLocation of
                Stack aOffset ->
                  emit [op' Op2{src = imm lit, dest = Mem{base = Rbp, offset = aOffset}}]
                Register aRegister ->
                  emit [op' Op2{src = imm lit, dest = aRegister}]
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

      instSelectionExpr_X86_64 varSizes rest
    Anf.IfThenElse cond then_ else_ rest -> do
      (condLocation, freeCondLocation) <-
        case cond of
          Anf.Name name ->
            error "TODO: instSelectionExpr_X86_64/IfThenElse/cond/Name" name
          Anf.Var var ->
            (,pure ()) <$> lookupLocation var
          Anf.Literal lit -> do
            location <- instSelectionLiteral_X86_64 lit
            pure (location, freeLocation location)
      case condLocation of
        Register register ->
          emit [cmp register (imm @Word64 0)]
        Stack offset ->
          emit [cmp Mem{base = Rbp, offset} (imm @Word64 0)]
      freeCondLocation

      (_thenLabel, beginThen) <- declareLabel "then"
      (elseLabel, beginElse) <- declareLabel "else"
      emit [je elseLabel]

      available <- gets (.available)

      beginThen
      _ <- instSelectionExpr_X86_64 varSizes then_
      modify (\s -> s{available})

      beginElse
      _ <- instSelectionExpr_X86_64 varSizes else_
      modify (\s -> s{available})

      instSelectionExpr_X86_64 varSizes rest
    Anf.Jump label arg -> do
      Log.trace "jump"
      Log.trace . Text.pack $ "  label: " <> show label
      Log.trace . Text.pack $ "  arg: " <> show arg

      labelArg <- lookupLabelArg label
      freeKills labelArg

      argLocation <- instSelectionSimple_X86_64 arg
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

      instSelectionExpr_X86_64 varSizes rest