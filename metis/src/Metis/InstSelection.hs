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
  instSelectionFunction_X86_64,

  -- * Internals
  Location (..),
  Value (..),
  Address (..),
  InstSelectionState (..),
  initialInstSelectionState,
  instSelectionExpr_X86_64,
  RegisterFunctionArgument (..),
  moveRegisterFunctionArguments,
) where

import Bound.Scope.Simple (instantiate)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (MonadReader, asks)
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad.State.Strict (State, StateT, runState, runStateT)
import Data.Buildable (collectL')
import Data.Foldable (for_, toList, traverse_)
import Data.Foldable.WithIndex (ifor_)
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
import Data.Traversable (for)
import Data.Word (Word64, Word8)
import GHC.Stack (HasCallStack)
import qualified Metis.Anf as Anf
import Metis.Asm (Block (..), BlockAttribute, Statement (..))
import qualified Metis.Asm as Asm (quad)
import Metis.Asm.Class (MonadAsm)
import qualified Metis.Asm.Class as Asm
import Metis.Isa (
  Add,
  Immediate,
  Instruction,
  Isa (generalPurposeRegisters),
  Lea,
  Memory (..),
  MemoryBase (..),
  Mov,
  Op2 (..),
  Register,
  Sub,
  Symbol (..),
  add,
  cmp,
  framePointerRegister,
  imm,
  je,
  jmp,
  lea,
  mov,
  pop,
  push,
  registerSize,
  ret,
  sub,
 )
import Metis.Isa.X86_64 (Register (..), X86_64, movb, movzbq)
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.Liveness (Liveness (..))
import Metis.Log (MonadLog)
import qualified Metis.Log as Log
import Metis.Type (Type)
import qualified Metis.Type as Type
import Witherable (forMaybe, wither)

data Location isa
  = Register (Register isa)
  | Stack {offset :: Int64}

deriving instance (Show (Register isa)) => Show (Location isa)
deriving instance (Eq (Register isa)) => Eq (Location isa)

data Value isa
  = Literal Literal
  | ValueAt (Location isa)
  | AddressOf (Address isa)

deriving instance (Show (Register isa)) => Show (Value isa)
deriving instance (Eq (Register isa)) => Eq (Value isa)

data Address isa
  = Symbol Symbol
  | Memory (Memory isa)

deriving instance (Show (Register isa)) => Show (Address isa)
deriving instance (Eq (Register isa)) => Eq (Address isa)

data InstSelectionState isa = InstSelectionState
  { nextStackOffset :: Int64
  , available :: Seq (Register isa)
  , locations :: Lazy.HashMap Anf.Var (Location isa)
  , labelArgLocations :: HashMap Anf.Var (Location isa)
  , liveness :: HashMap Anf.Var Liveness
  , typeDicts :: HashMap Symbol (Type Anf.Var)
  , previousBlocks :: [Block isa]
  , currentBlockName :: Text
  , currentBlockAttributes :: [BlockAttribute]
  , currentBlockStatements :: [Statement isa]
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
    , typeDicts = mempty
    , previousBlocks = []
    , currentBlockName = blockName
    , currentBlockAttributes = blockAttributes
    , currentBlockStatements = []
    }

lookupLocation :: (HasCallStack) => (MonadState (InstSelectionState isa) m) => Anf.Var -> m (Location isa)
lookupLocation var = gets (Maybe.fromMaybe (error $ show var <> "missing from location map") . HashMap.Lazy.lookup var . (.locations))

lookupLiveness :: (HasCallStack) => (MonadState (InstSelectionState isa) m) => Anf.Var -> m Liveness
lookupLiveness var = gets (Maybe.fromMaybe (error $ show var <> "missing from liveness map") . HashMap.lookup var . (.liveness))

lookupSize :: (HasCallStack) => Anf.Var -> HashMap Anf.Var Word64 -> Word64
lookupSize var varSizes = Maybe.fromMaybe (error $ show var <> " missing from sizes map") $ HashMap.lookup var varSizes

data InstSelectionEnv isa = InstSelectionEnv
  { labelArgs :: Anf.Var -> Anf.Var
  , labelArgLocations :: Lazy.HashMap Anf.Var (Location isa)
  , varKinds :: Anf.Var -> Kind
  , nameTys :: Text -> Type Anf.Var
  , varTys :: Anf.Var -> Type Anf.Var
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
  modify (\s -> s{currentBlockStatements = s.currentBlockStatements <> fmap Instruction instructions})

declareLabel ::
  (MonadState (InstSelectionState isa) m) =>
  Text ->
  m (Symbol, m ())
declareLabel value = do
  pure
    ( Metis.Isa.Symbol value
    , modify
        ( \s ->
            s
              { previousBlocks =
                  s.previousBlocks
                    <> [ Block
                          { label = s.currentBlockName
                          , attributes = s.currentBlockAttributes
                          , statements = s.currentBlockStatements
                          }
                       ]
              , currentBlockName = value
              , currentBlockAttributes = []
              , currentBlockStatements = []
              }
        )
    )

beginBlock ::
  (MonadState (InstSelectionState isa) m) =>
  Text ->
  m Symbol
beginBlock label =
  Metis.Isa.Symbol label
    <$ modify
      ( \s ->
          s
            { previousBlocks =
                s.previousBlocks
                  <> [ Block
                        { label = s.currentBlockName
                        , attributes = s.currentBlockAttributes
                        , statements = s.currentBlockStatements
                        }
                     ]
            , currentBlockName = label
            , currentBlockAttributes = []
            , currentBlockStatements = []
            }
      )

allocStack ::
  (MonadState (InstSelectionState isa) m) =>
  Word64 ->
  m Int64
allocStack size = do
  previousStackOffset <- gets (.nextStackOffset)
  let offset = previousStackOffset - fromIntegral @Word64 @Int64 size
  modify (\s -> s{nextStackOffset = offset})
  pure offset

allocLocation ::
  (MonadState (InstSelectionState isa) m) =>
  Word64 ->
  m (Location isa)
allocLocation size = do
  available <- gets (.available)
  case Seq.viewl available of
    Seq.EmptyL ->
      Stack <$> allocStack size
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

runInstSelectionT ::
  (MonadFix m) =>
  (Text -> Type Anf.Var) ->
  Anf.ExprInfo ->
  InstSelectionState isa ->
  ReaderT (InstSelectionEnv isa) (StateT (InstSelectionState isa) m) a ->
  m (a, InstSelectionState isa)
runInstSelectionT nameTys exprInfo s ma = do
  rec (a, s') <-
        runStateT
          ( runReaderT
              ma
              InstSelectionEnv
                { labelArgs = \label -> Maybe.fromMaybe (error $ "label " <> show label <> " missing from label args map") $ HashMap.lookup label exprInfo.labelArgs
                , labelArgLocations = s'.labelArgLocations
                , nameTys
                , varKinds = \var -> Maybe.fromMaybe (error $ "var " <> show var <> " missing from var kinds map") $ HashMap.lookup var exprInfo.varKinds
                , varTys = \var -> Maybe.fromMaybe (error $ "var " <> show var <> " missing from var types map") $ HashMap.lookup var exprInfo.varTys
                }
          )
          s
  pure (a, s')

instSelection_X86_64 ::
  (MonadAsm X86_64 m, MonadLog m, MonadFix m) =>
  (Text -> Type Anf.Var) ->
  Seq (Register X86_64) ->
  Anf.ExprInfo ->
  Anf.Expr ->
  HashMap Anf.Var Liveness ->
  Text ->
  [BlockAttribute] ->
  m (Value X86_64)
instSelection_X86_64 nameTys available exprInfo expr liveness blockName blockAttributes = do
  let initialState = initialInstSelectionState available liveness blockName blockAttributes
  (a, s) <- runInstSelectionT nameTys exprInfo initialState (instSelectionExpr_X86_64 mempty expr)
  ifor_ s.typeDicts generateTypeDict
  traverse_ (\Block{label, attributes, statements} -> Asm.block label attributes statements) s.previousBlocks
  _ <- Asm.block s.currentBlockName s.currentBlockAttributes s.currentBlockStatements
  pure a

instSelectionLiteral_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadLog m) =>
  Literal ->
  m (Value X86_64)
instSelectionLiteral_X86_64 lit =
  case lit of
    Literal.Uint64{} ->
      pure $ Literal lit
    Literal.Bool{} ->
      pure $ Literal lit

typeDict :: (MonadState (InstSelectionState X86_64) m, MonadLog m) => Type Anf.Var -> m Symbol
typeDict ty = do
  let label = Metis.Isa.Symbol{value = typeDictLabel ty}
  modify (\s -> s{typeDicts = HashMap.insert label ty s.typeDicts})
  pure label
  where
    typeDictLabel :: Type Anf.Var -> Text
    typeDictLabel t =
      case t of
        Type.Var{} ->
          error "impossible: can't generate type dict for variable"
        Type.Uint64 ->
          "type_Uint64"
        Type.Bool ->
          "type_Bool"
        Type.Fn{} ->
          "type_Fn"
        Type.Forall{} ->
          "type_Forall"
        Type.Ptr{} ->
          "type_Ptr"
        Type.Unit{} ->
          "type_Unit"
        Type.Unknown{} ->
          error "impossible: can't generate type dict for Unknown"

instSelectionType_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadLog m) =>
  Type Anf.Var ->
  m (Value X86_64)
instSelectionType_X86_64 ty = do
  case ty of
    Type.Var var ->
      ValueAt <$> lookupLocation var
    Type.Uint64 ->
      AddressOf . Metis.InstSelection.Symbol <$> typeDict ty
    Type.Bool ->
      AddressOf . Metis.InstSelection.Symbol <$> typeDict ty
    Type.Fn{} ->
      AddressOf . Metis.InstSelection.Symbol <$> typeDict ty
    Type.Forall{} ->
      AddressOf . Metis.InstSelection.Symbol <$> typeDict ty
    Type.Unit ->
      AddressOf . Metis.InstSelection.Symbol <$> typeDict ty
    Type.Ptr{} ->
      AddressOf . Metis.InstSelection.Symbol <$> typeDict ty
    Type.Unknown{} ->
      error "impossible: Unknown has no type dictionary"

instSelectionSimple_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadLog m) =>
  Anf.Simple ->
  m (Value X86_64)
instSelectionSimple_X86_64 simple =
  case simple of
    Anf.Var var ->
      ValueAt <$> lookupLocation var
    Anf.Literal lit ->
      instSelectionLiteral_X86_64 lit
    Anf.Type ty ->
      instSelectionType_X86_64 ty
    Anf.Name name ->
      pure . AddressOf $ Metis.InstSelection.Symbol Metis.Isa.Symbol{value = name}

freeVars :: (Isa isa, MonadState (InstSelectionState isa) m, MonadLog m) => HashSet Anf.Var -> m ()
freeVars vars = do
  locations <- gets (.locations)
  let freed =
        HashMap.Lazy.foldrWithKey'
          (\k v acc -> if k `HashSet.member` vars then v : acc else acc)
          []
          locations
  Log.trace . Text.pack $ "freed: " <> show freed

  modify
    ( \s ->
        s
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

freeKills :: (Isa isa, MonadState (InstSelectionState isa) m, MonadLog m) => Anf.Var -> m ()
freeKills var = do
  liveness <- lookupLiveness var
  Log.trace . Text.pack $ show var <> " kills " <> show liveness.kills

  freeVars liveness.kills

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
  { size :: Word64
  , src :: Value isa
  , dest :: Register isa
  }

data StackFunctionArgument isa = StackFunctionArgument
  { src :: Value isa
  , dest :: Memory isa
  }

setupFunctionArguments ::
  (MonadState (InstSelectionState X86_64) m) =>
  Seq (Register X86_64) ->
  [(Value X86_64, Kind)] ->
  [(Value X86_64, Type Anf.Var, Type Anf.Var)] ->
  m (FunctionArguments X86_64)
setupFunctionArguments availableArgumentRegisters typeArgs valueArgs =
  case Seq.viewl availableArgumentRegisters of
    register Seq.:< availableArgumentRegisters' ->
      case typeArgs of
        [] ->
          case valueArgs of
            [] ->
              pure mempty
            (argLocation, expectedArgTy, actualArgTy) : valueArgs' -> do
              -- create extra locals when necessary
              functionArgument <-
                case expectedArgTy of
                  Type.Var{} | (case actualArgTy of Type.Var{} -> False; _ -> True) -> do
                    offset <- allocStack $ Type.sizeOf actualArgTy
                    pure $
                      RegisterFunctionArgument
                        { size = Type.pointerSize
                        , src = AddressOf $ Memory Mem{base = BaseRegister Rbp, offset}
                        , dest = register
                        }
                  _ ->
                    pure $
                      RegisterFunctionArgument
                        { size = Type.sizeOf expectedArgTy
                        , src = argLocation
                        , dest = register
                        }
              ( ( case Type.callingConventionOf expectedArgTy of
                    Type.Register ->
                      FunctionArguments
                        { registerFunctionArguments = [functionArgument]
                        , stackFunctionArguments = []
                        }
                    Type.Composite{} -> error "TODO: types with composite calling conventions"
                    Type.Erased -> error "TODO: types with erased calling conventions"
                )
                  <>
                )
                <$> setupFunctionArguments
                  availableArgumentRegisters'
                  typeArgs
                  valueArgs'
        (typeArgValue, _typeArgKind) : typeArgs' ->
          ( FunctionArguments
              { registerFunctionArguments =
                  [ RegisterFunctionArgument
                      { size = Type.pointerSize
                      , src = typeArgValue
                      , dest = register
                      }
                  ]
              , stackFunctionArguments = []
              }
              <>
          )
            <$> setupFunctionArguments
              availableArgumentRegisters'
              typeArgs'
              valueArgs
    Seq.EmptyL ->
      setupStackFunctionArguments
        -- Assumes that 0(%rbp) in the callee's stack frame contains the return address, after which
        -- comes the stack arguments.
        (fromIntegral @Word64 @Int64 Type.pointerSize)
        typeArgs
        valueArgs

{-
The function arguments require all available registers, so the remaining arguments must be passed
on the stack.
-}
setupStackFunctionArguments ::
  (Applicative m) =>
  Int64 ->
  [(Value X86_64, Kind)] ->
  [(Value X86_64, Type Anf.Var, Type Anf.Var)] ->
  m (FunctionArguments X86_64)
setupStackFunctionArguments offset typeArgs valueArgs =
  case typeArgs of
    [] ->
      case valueArgs of
        [] ->
          pure mempty
        (argLocation, expectedArgTy, _actualArgTy) : valueArgs' ->
          ( ( case Type.callingConventionOf expectedArgTy of
                Type.Register ->
                  FunctionArguments
                    { registerFunctionArguments = []
                    , stackFunctionArguments = [StackFunctionArgument{src = argLocation, dest = Mem{base = BaseRegister Rbp, offset}}]
                    }
                Type.Composite{} -> error "TODO: types with composite calling conventions"
                Type.Erased -> error "TODO: types with erased calling conventions"
            )
              <>
          )
            <$> setupStackFunctionArguments
              (offset + fromIntegral @Word64 @Int64 (Type.sizeOf expectedArgTy))
              typeArgs
              valueArgs'
    (typeArgValue, _typeArgKind) : typeArgs' ->
      ( FunctionArguments
          { registerFunctionArguments = []
          , stackFunctionArguments = [StackFunctionArgument{src = typeArgValue, dest = Mem{base = BaseRegister Rbp, offset}}]
          }
          <>
      )
        <$> setupStackFunctionArguments
          (offset + fromIntegral @Word64 @Int64 Type.pointerSize)
          typeArgs'
          valueArgs

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
moveRegisterFunctionArguments registerRemapping arguments = do
  -- Any registers allocated here temporary; they will all be returned to the pool at the end of the function.
  available <- gets (.available)

  insts <-
    case arguments of
      [] ->
        pure []
      [RegisterFunctionArgument{size = _, src, dest}] ->
        case src of
          ValueAt (Register srcRegister) ->
            case HashMap.lookup srcRegister registerRemapping of
              Nothing ->
                pure [mov Op2{src = srcRegister, dest} | srcRegister /= dest]
              Just srcRegisterRemapped ->
                pure
                  [ case srcRegisterRemapped of
                    Register srcRegisterRemappedRegister ->
                      mov Op2{src = srcRegisterRemappedRegister, dest}
                    Stack srcRegisterRemappedOffset ->
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = srcRegisterRemappedOffset}, dest}
                  | srcRegisterRemapped /= Register dest
                  ]
          ValueAt (Stack srcOffset) ->
            pure [mov Op2{src = Mem{base = BaseRegister Rbp, offset = srcOffset}, dest}]
          AddressOf (Metis.InstSelection.Symbol symbol) ->
            pure [mov Op2{src = imm symbol, dest}]
          AddressOf (Memory mem) ->
            pure [lea Op2{src = mem, dest}]
          Literal lit ->
            pure [mov Op2{src = imm lit, dest}]
      RegisterFunctionArgument{size, src, dest} : arguments' -> do
        temp <- allocLocation size
        a <-
          case src of
            ValueAt (Register srcRegister) ->
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
                                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = srcRegisterRemappedOffset}, dest}
                                 ]
                  -- Even though the temporary registers are all freed at the end of this function,
                  -- they are freed incrementally so that the function uses a smaller set of
                  -- temporary registers.
                  freeLocation srcRegisterRemapped
                  pure a
            ValueAt (Stack srcOffset) ->
              pure $ saveDestination temp dest <> [mov Op2{src = Mem{base = BaseRegister Rbp, offset = srcOffset}, dest}]
            AddressOf (Metis.InstSelection.Symbol symbol) ->
              pure $ saveDestination temp dest <> [mov Op2{src = imm symbol, dest}]
            AddressOf (Memory mem) ->
              pure $ saveDestination temp dest <> [lea Op2{src = mem, dest}]
            Literal lit ->
              pure $ saveDestination temp dest <> [mov Op2{src = imm lit, dest}]

        b <- moveRegisterFunctionArguments (HashMap.insert dest temp registerRemapping) arguments'

        pure $ a <> b

  modify (\s -> s{available})

  pure insts
  where
    saveDestination temp dest =
      [ case temp of
          Register tempRegister ->
            mov Op2{src = dest, dest = tempRegister}
          Stack tempOffset ->
            mov Op2{src = dest, dest = Mem{base = BaseRegister Rbp, offset = tempOffset}}
      ]

getRegistersUsedByFunction ::
  forall isa.
  (Isa isa) =>
  Seq (Register isa) ->
  [Kind] ->
  [Type Anf.Var] ->
  Type Anf.Var ->
  HashSet (Register isa)
getRegistersUsedByFunction registerPool typeArgKinds argTys retTy =
  let
    ((), (_, toSave)) = flip runState (registerPool, mempty) $ do
      traverse_ goKind typeArgKinds
      traverse_ goType argTys
    -- TODO: stack-returned outputs need an input register
    ((), (_, toSave')) =
      runState (goType retTy) (registerPool, toSave)
   in
    toSave'
  where
    goKind :: Kind -> State (Seq (Register isa), HashSet (Register isa)) ()
    goKind _kind =
      -- Type arguments have "register" calling convention.
      -- A type argument is a pointer to a type dictionary.
      goCallingConventionRegister

    goType :: Type Anf.Var -> State (Seq (Register isa), HashSet (Register isa)) ()
    goType ty = goCallingConvention (Type.callingConventionOf ty)

    goCallingConvention :: Type.CallingConvention -> State (Seq (Register isa), HashSet (Register isa)) ()
    goCallingConvention cc =
      case cc of
        Type.Register ->
          goCallingConventionRegister
        Type.Composite ccs ->
          traverse_ goCallingConvention ccs
        Type.Erased ->
          error "TODO: goCallingConvention/Erased"

    goCallingConventionRegister :: State (Seq (Register isa), HashSet (Register isa)) ()
    goCallingConventionRegister = do
      availableRegisters <- gets fst
      case Seq.viewl availableRegisters of
        Seq.EmptyL -> pure mempty
        register Seq.:< availableRegisters' ->
          modify $ \(_, toSave) -> (availableRegisters', HashSet.insert register toSave)

generateTypeDict :: (MonadAsm X86_64 m) => Symbol -> Type a -> m Symbol
generateTypeDict name ty =
  case ty of
    Type.Var{} ->
      error "impossible: generating type dictionary for variable"
    Type.Unknown{} ->
      error "impossible: generating type dictionary for Unknown"
    Type.Uint64 -> do
      copy <-
        -- Type_Uint64_copy(self : *Type, from : *Uint64, to : *Uint64)
        Asm.block "Type_Uint64_copy" [] . fmap Instruction $
          [ mov Op2{src = Mem{base = BaseRegister Rbx, offset = 0}, dest = Rdx}
          , mov Op2{src = Rdx, dest = Mem{base = BaseRegister Rcx, offset = 0}}
          , mov Op2{src = Rcx, dest = Rax}
          , pop Rbp
          , ret ()
          ]
      Asm.struct
        name.value
        [ Asm.quad (8 :: Word64)
        , Asm.quad copy
        ]
    Type.Bool -> do
      copy <-
        Asm.block "Type_Bool_copy" [] . fmap Instruction $
          [ movzbq Op2{src = Mem{base = BaseRegister Rbx, offset = 0}, dest = Rdx}
          , movb Op2{src = Dl, dest = Mem{base = BaseRegister Rcx, offset = 0}}
          , mov Op2{src = Rcx, dest = Rax}
          , pop Rbp
          , ret ()
          ]
      Asm.struct
        name.value
        [ Asm.quad (1 :: Word64)
        , Asm.quad copy
        ]
    Type.Fn{} -> do
      copy <-
        Asm.block "Type_Fn_copy" [] . fmap Instruction $
          [ mov Op2{src = Mem{base = BaseRegister Rbx, offset = 0}, dest = Rdx}
          , mov Op2{src = Rdx, dest = Mem{base = BaseRegister Rcx, offset = 0}}
          , mov Op2{src = Rcx, dest = Rax}
          , pop Rbp
          , ret ()
          ]
      Asm.struct
        name.value
        [ Asm.quad (8 :: Word64)
        , Asm.quad copy
        ]
    Type.Forall{} -> do
      copy <-
        Asm.block "Type_Forall_copy" [] . fmap Instruction $
          [ mov Op2{src = Mem{base = BaseRegister Rbx, offset = 0}, dest = Rdx}
          , mov Op2{src = Rdx, dest = Mem{base = BaseRegister Rcx, offset = 0}}
          , mov Op2{src = Rcx, dest = Rax}
          , pop Rbp
          , ret ()
          ]
      Asm.block
        name.value
        []
        [ Directive $ Asm.quad (8 :: Word64)
        , Directive $ Asm.quad copy
        ]
    Type.Unit -> do
      copy <-
        Asm.block "Type_Unit_copy" [] $ fmap Instruction [pop Rbp, ret ()]
      Asm.block
        name.value
        []
        [ Directive $ Asm.quad (0 :: Word64)
        , Directive $ Asm.quad copy
        ]
    Type.Ptr{} ->
      error "TODO: generateTypeDict/Ptr"

-- | Store an 8-byte value in the pointer held by a location.
storeq :: (MonadState (InstSelectionState X86_64) m) => Value X86_64 -> Location X86_64 -> m ()
storeq value destination = do
  available <- gets (.available)
  emit $
    case value of
      ValueAt (Register register) ->
        case destination of
          Register destinationRegister ->
            [mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}]
          Stack destinationOffset ->
            case Seq.viewl available of
              Seq.EmptyL ->
                let destinationRegister = Rax
                 in [ push destinationRegister
                    , -- load pointer from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                    , -- store value to pointer
                      mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                    , pop destinationRegister
                    ]
              destinationRegister Seq.:< _ ->
                [ -- load pointer from memory
                  mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                , -- store value to pointer
                  mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                ]
      ValueAt (Stack offset) ->
        case destination of
          Register destinationRegister ->
            case Seq.viewl available of
              Seq.EmptyL ->
                let register = Rax
                 in [ push register
                    , -- load value from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = register}
                    , -- store value to pointer
                      mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                    , pop register
                    ]
              register Seq.:< _ ->
                [ -- load value from memory
                  mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = register}
                , -- store value to pointer
                  mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                ]
          Stack destinationOffset ->
            case Seq.viewl available of
              Seq.EmptyL ->
                let register = Rax
                    destinationRegister = Rbx
                 in [ push register
                    , push destinationRegister
                    , -- load value from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = register}
                    , -- load pointer from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                    , -- store value to pointer
                      mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                    , pop destinationRegister
                    , pop register
                    ]
              register Seq.:< available' ->
                case Seq.viewl available' of
                  Seq.EmptyL ->
                    let destinationRegister = Rax
                     in [ push destinationRegister
                        , -- load value from memory
                          mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = register}
                        , -- load pointer from memory
                          mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                        , -- store value to pointer
                          mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                        , pop destinationRegister
                        ]
                  destinationRegister Seq.:< _ ->
                    [ -- load value from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = register}
                    , -- load pointer from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                    , -- store value to pointer
                      mov Op2{src = register, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                    ]
      AddressOf (Metis.InstSelection.Symbol label) ->
        case destination of
          Register destinationRegister ->
            [mov Op2{src = imm label, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}]
          Stack destinationOffset ->
            case Seq.viewl available of
              Seq.EmptyL ->
                let destinationRegister = Rax
                 in [ push destinationRegister
                    , -- load pointer from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                    , -- store value to pointer
                      mov Op2{src = imm label, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                    , pop destinationRegister
                    ]
              destinationRegister Seq.:< _ ->
                [ -- load pointer from memory
                  mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                , -- store value to pointer
                  mov Op2{src = imm label, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                ]
      AddressOf (Memory mem) ->
        error "TODO: storeq AddressOf/Memory" mem
      Literal lit ->
        case destination of
          Register destinationRegister ->
            [mov Op2{src = imm lit, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}]
          Stack destinationOffset ->
            case Seq.viewl available of
              Seq.EmptyL ->
                let destinationRegister = Rax
                 in [ push destinationRegister
                    , -- load pointer from memory
                      mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                    , -- store value to pointer
                      mov Op2{src = imm lit, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                    , pop destinationRegister
                    ]
              destinationRegister Seq.:< _ ->
                [ -- load pointer from memory
                  mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
                , -- store value to pointer
                  mov Op2{src = imm lit, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
                ]

{-
case destination of
  Register destinationRegister ->
    [lea Op2{src = mem, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}]
  Stack destinationOffset ->
    case Seq.viewl available of
      Seq.EmptyL ->
        let destinationRegister = Rax
         in [ push destinationRegister
            , -- load pointer from memory
              mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
            , -- store value to pointer
              lea Op2{src = mem, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
            , pop destinationRegister
            ]
      destinationRegister Seq.:< _ ->
        [ -- load pointer from memory
          mov Op2{src = Mem{base = BaseRegister Rbp, offset = destinationOffset}, dest = destinationRegister}
        , -- store value to pointer
          lea Op2{src = mem, dest = Mem{base = BaseRegister destinationRegister, offset = 0}}
        ]
-}

copyValue ::
  (MonadState (InstSelectionState X86_64) m) =>
  -- | The type of the value that's being copied.
  Type Anf.Var ->
  -- | The source value.
  Value X86_64 ->
  -- | Contains a pointer into which we should copy the source value.
  Location X86_64 ->
  m (Location X86_64)
copyValue ty value outputLocation =
  case ty of
    Type.Var var -> do
      -- When working with a type variable, `value` is a pointer. We use the type
      -- variable's type dictionary to copy the contents of the pointer to the destination.
      varLocation <- lookupLocation var

      (after, emitAfter) <- declareLabel "after"
      emit [push (imm after)]

      -- TODO: this does not save call-clobbered registers. it's currently safe because it's only
      -- used when a function is returning, and no registers are by a function after its return
      -- instruction.

      emit $
        case varLocation of
          Register register ->
            [mov Op2{src = register, dest = Rax} | register /= Rax]
          Stack offset ->
            [mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = Rax}]
      emit $
        case value of
          ValueAt (Register register) ->
            [mov Op2{src = register, dest = Rbx} | register /= Rbx]
          ValueAt (Stack offset) ->
            [mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = Rbx}]
          AddressOf (Metis.InstSelection.Symbol label) ->
            [mov Op2{src = imm label, dest = Rbx}]
          AddressOf (Memory mem) ->
            [lea Op2{src = mem, dest = Rbx}]
          Literal lit ->
            [mov Op2{src = imm lit, dest = Rbx}]

      emit $
        case outputLocation of
          Register register ->
            [mov Op2{src = register, dest = Rcx} | register /= Rcx]
          Stack offset ->
            [mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = Rcx}]
      emit
        [ push Rbp
        , mov Op2{src = Rsp, dest = Rbp}
        , mov
            Op2
              { src =
                  Mem
                    { base = BaseRegister Rax
                    , -- offset of `copy` function
                      offset = 8
                    }
              , dest = Rdx
              }
        , jmp Rdx
        ]

      emitAfter

      -- The type copy functions return the output pointer in `rax`.
      pure $ Register Rax
    Type.Bool ->
      error "TODO: storeb value outputLocation" value outputLocation
    Type.Uint64 -> do
      storeq value outputLocation
      pure outputLocation
    Type.Fn{} -> do
      storeq value outputLocation
      pure outputLocation
    Type.Forall{} -> do
      storeq value outputLocation
      pure outputLocation
    Type.Unit ->
      error "TODO: copyValue/Unit"
    Type.Ptr{} ->
      error "TODO: copyValue/Ptr"
    Type.Unknown ->
      error "impossible: can't copy Unknown"

instSelectionFunction_X86_64 ::
  (MonadAsm X86_64 m, MonadLog m, MonadFix m) =>
  (Text -> Type Anf.Var) ->
  Seq (Register X86_64) ->
  HashMap Anf.Var Liveness ->
  Anf.Function ->
  m ()
instSelectionFunction_X86_64 nameTys initialAvailable liveness function = do
  let initial = initialInstSelectionState initialAvailable liveness function.name []
  rec let localsSize = fromIntegral @Int64 @Word64 (-s'.nextStackOffset)
      ((), s') <- runInstSelectionT nameTys function.bodyInfo initial $ do
        (stackArgumentsSize, mOutputLocation) <- setupArguments function.tyArgs function.args function.retTy
        emit [sub Op2{dest = Rsp, src = imm localsSize} | localsSize > 0]
        value <- instSelectionExpr_X86_64 mempty function.body
        case mOutputLocation of
          Just outputLocation -> do
            -- `outputLocation` is a function argument containing a pointer to (caller-allocated)
            -- memory where the function's result should be saved. It's used when a function needs
            -- to return a value via the stack instead of a register.
            value' <- copyValue function.retTy value outputLocation
            emit $
              case value' of
                Register register ->
                  [mov Op2{src = register, dest = Rax} | register /= Rax]
                Stack offset ->
                  [mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = Rax}]
          Nothing ->
            case Type.callingConventionOf function.retTy of
              Type.Register ->
                emit $
                  case value of
                    ValueAt (Register register) ->
                      [mov Op2{src = register, dest = Rax} | register /= Rax]
                    ValueAt (Stack offset) ->
                      [mov Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = Rax}]
                    AddressOf (Metis.InstSelection.Symbol label) ->
                      [mov Op2{src = imm label, dest = Rax}]
                    AddressOf (Memory mem) ->
                      [lea Op2{src = mem, dest = Rax}]
                    Literal lit ->
                      [mov Op2{src = imm lit, dest = Rax}]
              Type.Composite{} -> error "TODO: composite return values"
              Type.Erased -> error "TODO: erased return values"
        emit $
          [add Op2{dest = Rsp, src = imm localsSize} | localsSize > 0]
            <> [pop Rbp]
            -- TODO: have caller put return address *after* the stack arguments, then use `ret
            -- stackArgumentsSize`, which pops the return address into `rip` then releases
            -- `stackArgumentsSize` bytes from the stack.
            <> [add Op2{dest = Rsp, src = imm stackArgumentsSize} | stackArgumentsSize > 0]
            <> [ret ()]

  ifor_ s'.typeDicts generateTypeDict

  traverse_
    (\Block{label, attributes, statements} -> Asm.block label attributes statements)
    s'.previousBlocks

  _ <-
    Asm.block
      s'.currentBlockName
      s'.currentBlockAttributes
      s'.currentBlockStatements

  pure ()
  where
    -- TODO: this code is basically the same as `setupFunctionArguments`. Make it the same code?
    setupArguments ::
      (MonadState (InstSelectionState isa) m) =>
      [(Anf.Var, Kind)] ->
      [(Anf.Var, Type Anf.Var)] ->
      Type Anf.Var ->
      m (Word64, Maybe (Location isa))
    setupArguments tyArgs args retTy =
      case tyArgs of
        tyArg : tyArgs' -> do
          available <- gets (.available)
          case Seq.viewl available of
            register Seq.:< available' -> do
              modify
                ( \s ->
                    s
                      { available = available'
                      , locations = HashMap.insert (fst tyArg) (Register register) s.locations
                      }
                )
              setupArguments tyArgs' args retTy
            Seq.EmptyL ->
              setupStackArguments
                (fromIntegral @Word64 @Int64 Type.pointerSize)
                0
                tyArgs
                args
                retTy
        [] ->
          case args of
            [] -> do
              case retTy of
                Type.Var{} -> do
                  available <- gets (.available)
                  case Seq.viewl available of
                    register Seq.:< available' -> do
                      modify (\s -> s{available = available'})
                      pure (0, Just $ Register register)
                    Seq.EmptyL ->
                      setupStackArguments
                        (fromIntegral @Word64 @Int64 Type.pointerSize)
                        0
                        tyArgs
                        args
                        retTy
                _ ->
                  pure (0, Nothing)
            arg : args' -> do
              case Type.callingConventionOf $ snd arg of
                Type.Register -> do
                  available <- gets (.available)
                  case Seq.viewl available of
                    register Seq.:< available' -> do
                      modify
                        ( \s ->
                            s
                              { available = available'
                              , locations = HashMap.insert (fst arg) (Register register) s.locations
                              }
                        )
                      setupArguments tyArgs args' retTy
                    Seq.EmptyL ->
                      setupStackArguments
                        (fromIntegral @Word64 @Int64 Type.pointerSize)
                        0
                        tyArgs
                        args -- we couldn't allocate register for `arg`, so try again with the stack
                        retTy
                Type.Composite{} ->
                  error "TODO: composite function arguments"
                Type.Erased ->
                  error "TODO: erased function arguments"

    setupStackArguments ::
      (MonadState (InstSelectionState isa) m) =>
      Int64 ->
      Word64 ->
      [(Anf.Var, Kind)] ->
      [(Anf.Var, Type Anf.Var)] ->
      Type Anf.Var ->
      m (Word64, Maybe (Location isa))
    setupStackArguments offset size tyArgs args retTy =
      case tyArgs of
        (tyArgVar, _tyArgKind) : tyArgs' -> do
          modify (\s -> s{locations = HashMap.insert tyArgVar (Stack offset) s.locations})
          let tyArgSize = Type.pointerSize
          setupStackArguments
            (offset + fromIntegral @Word64 @Int64 tyArgSize)
            (size + tyArgSize)
            tyArgs'
            args
            retTy
        [] ->
          case args of
            [] -> do
              case retTy of
                Type.Var{} ->
                  pure (size + Type.pointerSize, Just $ Stack offset)
                _ ->
                  pure (size, Nothing)
            (argVar, argTy) : args' ->
              case Type.callingConventionOf argTy of
                Type.Register -> do
                  modify (\s -> s{locations = HashMap.insert argVar (Stack offset) s.locations})
                  let argTySize = Type.sizeOf argTy
                  setupStackArguments
                    (offset + fromIntegral @Word64 @Int64 argTySize)
                    (size + argTySize)
                    tyArgs
                    args'
                    retTy
                Type.Composite{} -> error "TODO: composite stack function arguments"
                Type.Erased -> error "TODO: erased stack function arguments"

instSelectionExpr_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  HashMap Anf.Var Word64 ->
  Anf.Expr ->
  m (Value X86_64)
instSelectionExpr_X86_64 varSizes expr =
  case expr of
    Anf.Return simple ->
      instSelectionSimple_X86_64 simple
    Anf.LetS var ty value rest -> do
      freeKills var

      valueLocation <-
        case value of
          Anf.Var var' ->
            lookupLocation var'
          Anf.Literal lit -> do
            location <- allocLocation $ Type.sizeOf ty
            case location of
              Stack offset -> do
                emit [mov Op2{src = imm lit, dest = Mem{base = BaseRegister Rbp, offset}}]
                pure location
              Register register -> do
                emit [mov Op2{src = imm lit, dest = register}]
                pure location
          Anf.Name{} ->
            error "TODO: instSelectionExpr_X86_64/Name"
          Anf.Type{} ->
            error "TODO: instSelectionExpr_X86_64/Type"
      modify (\s -> s{locations = HashMap.Lazy.insert var valueLocation s.locations})

      instSelectionExpr_X86_64 varSizes rest
    Anf.LetC var _varInfo value rest -> do
      Log.trace "LetC"
      Log.trace . Text.pack $ "  var: " <> show var
      Log.trace . Text.pack $ "  value: " <> show value

      case value of
        Anf.Call function args ->
          instSelectionCall_X86_64 var function args
        Anf.Binop op a b -> do
          let op' :: (Add X86_64 a b, Sub X86_64 a b) => Op2 a b -> Instruction X86_64
              op' =
                case op of
                  Anf.Add -> add
                  Anf.Subtract -> sub

          -- Binop convention: the first argument is the "destination". Motivated by subtraction
          -- in assembly, which is `dest := dest - src`.
          liveness <- lookupLiveness var
          aLocation <-
            case a of
              Anf.Name name ->
                error "TODO: instSelectionExpr_X86_64/Binop/a/Name" name
              Anf.Type ty ->
                error "TODO: instSelectionExpr_X86_64/Binop/a/Type" ty
              Anf.Literal lit -> do
                location <- allocLocation . Type.sizeOf $ Literal.typeOf lit
                lit' <- instSelectionLiteral_X86_64 lit
                mov_vl lit' location
                pure location
              Anf.Var aVar -> do
                aLocation <- lookupLocation aVar

                {- In an A-normal form instruction like `%1 = add(%2, %3)`, `%1` and `%2`
                need to be assigned the same location. The fast path is when `%1` kills `%2`:
                after the instruction `%2` is no longer relevant, so `%1` can steal `%2`'s
                location.

                When `%1` *doesn't* kill `%2`, we have to assign a fresh location to `%1` and
                move the contents of `%2` to this location before executing the instruction.
                `%2` is still relevant later on so we have to preserve its value.
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
                        emit [mov Op2{src = aRegister, dest = Mem{base = BaseRegister Rbp, offset = aOffset'}}]
                      (Stack aOffset, Register aRegister') ->
                        emit [mov Op2{src = Mem{base = BaseRegister Rbp, offset = aOffset}, dest = aRegister'}]
                      (Stack aOffset, Stack aOffset') ->
                        emit
                          [ push Rax
                          , mov Op2{src = Mem{base = BaseRegister Rbp, offset = aOffset}, dest = Rax}
                          , mov Op2{src = Rax, dest = Mem{base = BaseRegister Rbp, offset = aOffset'}}
                          , pop Rax
                          ]
                pure aLocation

          case b of
            Anf.Name name ->
              error "TODO: instSelectionExpr_X86_64/Binop/b/Name" name
            Anf.Type ty ->
              error "TODO: instSelectionExpr_X86_64/Binop/b/Type" ty
            Anf.Literal lit -> do
              case aLocation of
                Stack aOffset ->
                  emit [op' Op2{src = imm lit, dest = Mem{base = BaseRegister Rbp, offset = aOffset}}]
                Register aRegister ->
                  emit [op' Op2{src = imm lit, dest = aRegister}]
            Anf.Var bVar -> do
              bLocation <- lookupLocation bVar
              emit $ case (aLocation, bLocation) of
                (Register aRegister, Register bRegister) ->
                  [op' Op2{dest = aRegister, src = bRegister}]
                (Register aRegister, Stack bOffset) ->
                  [op' Op2{dest = aRegister, src = Mem{base = BaseRegister Rbp, offset = bOffset}}]
                (Stack aOffset, Register bRegister) -> do
                  [op' Op2{dest = Mem{base = BaseRegister Rbp, offset = aOffset}, src = bRegister}]
                (Stack aOffset, Stack bOffset) ->
                  [ push Rax
                  , mov Op2{src = Mem{base = BaseRegister Rbp, offset = bOffset}, dest = Rax}
                  , op' Op2{dest = Mem{base = BaseRegister Rbp, offset = aOffset}, src = Rax}
                  , pop Rax
                  ]

          freeVars $
            case a of
              Anf.Var aVar ->
                {- When `a` is a variable we don't return its register to the pool.

                If the variable is killed by this instruction, we have its register as the
                destination for the instruction.

                If the variable is not killed by this instruction, we have made sure its value
                is preserved. When the value is preserved in a register, that register can't be
                returned to the pool.
                -}
                HashSet.delete aVar liveness.kills
              Anf.Name{} ->
                liveness.kills
              Anf.Literal{} ->
                liveness.kills
              Anf.Type{} ->
                liveness.kills
          modify (\s -> s{locations = HashMap.Lazy.insert var aLocation s.locations})
        Anf.Alloca ty ->
          instSelectionAlloca_X86_64 var ty
        Anf.Store ptr val ->
          instSelectionStore_X86_64 var ptr val
        Anf.Load ptr ->
          instSelectionLoad_X86_64 var ptr
        Anf.GetField ptr field ->
          instSelectionGetField_X86_64 var ptr field

      instSelectionExpr_X86_64 varSizes rest
    Anf.IfThenElse cond then_ else_ rest -> do
      (condLocation, freeCondLocation) <-
        case cond of
          Anf.Name name ->
            error "TODO: instSelectionExpr_X86_64/IfThenElse/cond/Name" name
          Anf.Type ty ->
            error "TODO: instSelectionExpr_X86_64/IfThenElse/cond/Type" ty
          Anf.Var var ->
            (,pure ()) <$> lookupLocation var
          Anf.Literal lit -> do
            location <- allocLocation . Type.sizeOf $ Literal.typeOf lit
            lit' <- instSelectionLiteral_X86_64 lit
            mov_vl lit' location
            pure (location, freeLocation location)
      case condLocation of
        Register register ->
          emit [cmp register (imm @Word64 0)]
        Stack offset ->
          emit [cmp Mem{base = BaseRegister Rbp, offset} (imm @Word64 0)]
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

      argValue <- instSelectionSimple_X86_64 arg
      labelArgLocation <- lookupLabelArgLocation label
      emit $
        -- If we're jumping forward to a label then `labelArgLocation` isn't known yet. It will be
        -- computed when we examine the corresponding block. Therefore we can't `emit` based on
        -- the value of `labelArgLocation`. The inspection of `labelArgLocation` has to be delayed
        -- until after we've examined the whole expression.
        if argValue == ValueAt labelArgLocation
          then []
          else case (argValue, labelArgLocation) of
            (ValueAt (Register argRegister), Register labelArgRegister) ->
              [mov Op2{src = argRegister, dest = labelArgRegister}]
            (ValueAt (Register argRegister), Stack labelArgOffset) ->
              [mov Op2{src = argRegister, dest = Mem{base = BaseRegister Rbp, offset = labelArgOffset}}]
            (ValueAt (Stack argOffset), Register labelArgRegister) -> do
              [mov Op2{src = Mem{base = BaseRegister Rbp, offset = argOffset}, dest = labelArgRegister}]
            (ValueAt (Stack argOffset), Stack labelArgOffset) ->
              [ push Rax
              , mov Op2{src = Mem{base = BaseRegister Rbp, offset = argOffset}, dest = Rax}
              , mov Op2{src = Rax, dest = Mem{base = BaseRegister Rbp, offset = labelArgOffset}}
              , pop Rax
              ]
            (AddressOf (Metis.InstSelection.Symbol symbol), Register labelArgRegister) -> do
              [mov Op2{src = imm symbol, dest = labelArgRegister}]
            (AddressOf (Metis.InstSelection.Symbol symbol), Stack labelArgOffset) ->
              [mov Op2{src = imm symbol, dest = Mem{base = BaseRegister Rbp, offset = labelArgOffset}}]
            (AddressOf (Memory mem), Register labelArgRegister) -> do
              [lea Op2{src = mem, dest = labelArgRegister}]
            (AddressOf (Memory mem), Stack labelArgOffset) ->
              [ push Rax
              , lea Op2{src = mem, dest = Rax}
              , mov Op2{src = Rax, dest = Mem{base = BaseRegister Rbp, offset = labelArgOffset}}
              , pop Rax
              ]
            (Literal lit, Register labelArgRegister) ->
              [mov Op2{src = imm lit, dest = labelArgRegister}]
            (Literal lit, Stack labelArgOffset) ->
              [mov Op2{src = imm lit, dest = Mem{base = BaseRegister Rbp, offset = labelArgOffset}}]

      emit [jmp $ Metis.Isa.Symbol . Text.pack $ "block_" <> show label.value]
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

data ClassifiedArguments isa = ClassifiedArguments
  { typeArgs :: [(Value isa, Kind)]
  , args :: [(Value isa, Type Anf.Var, Type Anf.Var)]
  , retTy :: Type Anf.Var
  }

classifyArguments ::
  (Isa isa) =>
  (Anf.Var -> Kind) ->
  (Text -> Type Anf.Var) ->
  (Anf.Var -> Type Anf.Var) ->
  Type Anf.Var ->
  [(Anf.Simple, Value isa)] ->
  ClassifiedArguments isa
classifyArguments varKinds nameTys varTys ty args =
  case ty of
    Type.Forall tyVars body ->
      let
        (usedArgs, args') = splitAt (length tyVars) args
        usedTypeArgs =
          fmap
            ( \(simple, _location) ->
                case simple of
                  Anf.Type tyArg -> tyArg
                  arg -> error $ "expected type argument, got " <> show arg
            )
            usedArgs
        result = classifyArguments varKinds nameTys varTys (instantiate (\index -> usedTypeArgs !! fromIntegral @Word64 @Int index) body) args'
       in
        result{typeArgs = zipWith (\(_, location) (_, argTy) -> (location, argTy)) usedArgs tyVars <> result.typeArgs}
    Type.Fn argTys retTy ->
      if length argTys /= length args
        then
          error $
            "incorrect number of arguments supplied to function. expected "
              <> show (length argTys)
              <> ", got "
              <> show (length args)
              <> "("
              <> show args
              <> ")"
        else
          ClassifiedArguments
            { typeArgs = []
            , args =
                zipWith
                  ( \(simple, location) expectedArgTy ->
                      ( location
                      , expectedArgTy
                      , either
                          (error . ("expected type, got kind: " <>) . show)
                          id
                          (Anf.typeOf varKinds nameTys varTys simple)
                      )
                  )
                  args
                  argTys
            , retTy
            }
    _ ->
      ClassifiedArguments{typeArgs = [], args = [], retTy = ty}

instSelectionCall_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  Anf.Var ->
  Anf.Simple ->
  [Anf.Simple] ->
  m ()
instSelectionCall_X86_64 var function args = do
  functionLocation <- instSelectionSimple_X86_64 function
  argLocations <- traverse instSelectionSimple_X86_64 args

  varKinds <- asks (.varKinds)
  nameTys <- asks (.nameTys)
  varTys <- asks (.varTys)
  case Anf.typeOf varKinds nameTys varTys function of
    Right ty -> do
      let ClassifiedArguments{typeArgs, args = valueArgs, retTy} = classifyArguments varKinds nameTys varTys ty (zip args argLocations)

      registersAvailableAtCall <- collectL' @(HashSet _) <$> gets (.available)
      registersKilledByCall <- do
        liveness <- lookupLiveness var
        HashSet.fromList
          <$> wither
            ( \killedVar -> do
                location <- lookupLocation killedVar
                case location of
                  Register register -> pure $ Just register
                  Stack{} -> pure Nothing
            )
            (HashSet.toList liveness.kills)
      let registersUsedByFunction =
            getRegistersUsedByFunction
              (generalPurposeRegisters @X86_64)
              (fmap snd typeArgs)
              (fmap (\(_, x, _) -> x) valueArgs)
              retTy

      callerSavedRegisters <-
        forMaybe (generalPurposeRegisters @X86_64) $ \register ->
          if not (register `HashSet.member` registersAvailableAtCall)
            && not (register `HashSet.member` registersKilledByCall)
            && register `HashSet.member` registersUsedByFunction
            then Just register <$ emit [push register]
            else pure Nothing

      (label, emitLabel) <- declareLabel "after"
      emit [push (imm label)]

      functionArguments <-
        setupFunctionArguments
          (generalPurposeRegisters @X86_64)
          typeArgs
          valueArgs

      emit =<< moveRegisterFunctionArguments mempty functionArguments.registerFunctionArguments

      for_ (reverse functionArguments.stackFunctionArguments) $ \StackFunctionArgument{src, dest = _} -> do
        available <- gets (.available)
        emit $
          case src of
            ValueAt (Register register) ->
              [push register]
            ValueAt (Stack offset) ->
              [push Mem{base = BaseRegister Rbp, offset}]
            AddressOf (Metis.InstSelection.Symbol symbol) ->
              [push (imm symbol)]
            AddressOf (Memory mem) ->
              case Seq.viewl available of
                Seq.EmptyL ->
                  [ sub Op2{src = imm (8 :: Word64), dest = Rsp}
                  , push Rax
                  , lea Op2{src = mem, dest = Rax}
                  , mov Op2{src = Rax, dest = Mem{base = BaseRegister Rsp, offset = 8}}
                  , pop Rax
                  ]
                register Seq.:< _ ->
                  [lea Op2{src = mem, dest = register}, push register]
            Literal lit ->
              [push (imm lit)]

      emit [push Rbp]
      emit [mov Op2{src = Rsp, dest = Rbp}]

      available <- gets (.available)
      emit $
        case functionLocation of
          ValueAt (Register register) ->
            [jmp register]
          ValueAt (Stack offset) ->
            [jmp Mem{base = BaseRegister Rbp, offset}]
          AddressOf (Metis.InstSelection.Symbol symbol) ->
            [jmp symbol]
          AddressOf (Memory mem) ->
            case Seq.viewl available of
              Seq.EmptyL ->
                error "TODO: jump to address of memory when no registers available"
              register Seq.:< _ ->
                [lea Op2{src = mem, dest = register}, jmp register]
          Literal{} ->
            error "cannot jump to literal"

      emitLabel
      freeKills var

      {- At this point, the callee should have cleaned up. It will have:

      1. Popped all stack function arguments popped
      2. Popped caller's frame pointer to `%rbp`
      3. Popped and jumped to return address

      The following code is written under these assumptions.
      -}
      case Type.callingConventionOf retTy of
        Type.Register -> do
          location <-
            if Rax `HashSet.member` registersAvailableAtCall || Rax `HashSet.member` registersKilledByCall
              then do
                modify (\s -> s{available = Seq.filter (/= Rax) s.available})
                pure $ Register Rax
              else do
                -- If the register was not available at the call site, then it was
                -- caller-saved. We have to move the result to a new register so we can
                -- restore the caller-saved register later.
                location <- allocLocation $ Type.sizeOf retTy
                emit
                  [ case location of
                      Register register -> mov Op2{src = Rax, dest = register}
                      Stack offset -> mov Op2{src = Rax, dest = Mem{base = BaseRegister Rbp, offset}}
                  ]
                pure location
          modify (\s -> s{locations = HashMap.insert var location s.locations})
        Type.Composite{} ->
          error "TODO: composite return types"
        Type.Erased ->
          error "TODO: erased return types"

      for_ (Seq.reverse callerSavedRegisters) $ \register -> emit [pop register]
    ty -> error $ "trying to call a non-function type: " <> show ty

instSelectionAlloca_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  Anf.Var ->
  Type Anf.Var ->
  m ()
instSelectionAlloca_X86_64 var ty = do
  location <-
    case ty of
      Type.Var{} ->
        error "TODO: Alloca/Var"
      Type.Uint64 ->
        allocaKnown ty
      Type.Bool ->
        allocaKnown ty
      Type.Unit ->
        error "TODO: Alloca/Unit"
      Type.Fn{} -> do
        allocaKnown ty
      Type.Forall{} -> do
        allocaKnown ty
      Type.Ptr{} -> do
        allocaKnown ty
      Type.Unknown{} -> do
        error "impossible: can't allocate for Unknown"
  modify (\s -> s{locations = HashMap.Lazy.insert var location s.locations})
  where
    allocaKnown ty' = do
      offset <- allocStack $ Type.sizeOf ty'
      location <- allocLocation Type.pointerSize
      available <- gets (.available)
      emit $
        case location of
          Register locationRegister ->
            [lea Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = locationRegister}]
          Stack locationOffset ->
            case Seq.viewl available of
              Seq.EmptyL ->
                let locationRegister = Rax
                 in [ push locationRegister
                    , lea Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = locationRegister}
                    , mov Op2{src = locationRegister, dest = Mem{base = BaseRegister Rbp, offset = locationOffset}}
                    , pop locationRegister
                    ]
              locationRegister Seq.:< _ ->
                [ lea Op2{src = Mem{base = BaseRegister Rbp, offset}, dest = locationRegister}
                , mov Op2{src = locationRegister, dest = Mem{base = BaseRegister Rbp, offset = locationOffset}}
                ]
      pure location

allocTempRegisters ::
  forall isa m.
  ( MonadState (InstSelectionState isa) m
  , Isa isa
  , Mov isa (Memory isa) (Register isa)
  , Mov isa (Register isa) (Memory isa)
  ) =>
  Word8 ->
  m ([Register isa], m ())
allocTempRegisters n =
  if n == 0
    then pure ([], pure ())
    else do
      available <- gets (.available)
      case Seq.viewl available of
        Seq.EmptyL -> do
          let n' = fromIntegral @Word8 @Int n
          let registers = generalPurposeRegisters @isa
          let registersLength = length registers
          if n' <= registersLength
            then do
              let allocated = toList $ Seq.take n' registers
              registersAndOffsets <-
                for allocated $ \register -> do
                  offset <- allocStack (registerSize @isa)
                  emit [mov Op2{src = register, dest = Mem{base = BaseRegister $ framePointerRegister @isa, offset}}]
                  pure (register, offset)
              pure
                ( allocated
                , traverse_
                    (\(register, offset) -> emit [mov Op2{src = Mem{base = BaseRegister $ framePointerRegister @isa, offset}, dest = register}])
                    registersAndOffsets
                )
            else
              error $
                "tried to allocate "
                  <> show n'
                  <> " registers, but only "
                  <> show registersLength
                  <> " available: "
                  <> show registers
        register Seq.:< available' -> do
          modify (\s -> s{available = available'})
          (registers, free) <- allocTempRegisters (n - 1)
          pure
            ( register : registers
            , free *> modify (\s -> s{available = register Seq.<| s.available})
            )

{- | Allocate a temporary register. Returns the allocated register and an action that will "free"
the register. The "free" action must be called when the register is no longer in use.

"Nested" (successive calls without a call to "free" in between) calls to 'allocTempRegister' are
invalid because of the way it spills when no registers are available.
When no registers are available, 'allocTempRegister' picks the first of 'generalPurposeRegisters' as
the target register.
The existing contents of this register are saved to stack memory and restored after the callback.
On 'X86_64', a "nested" 'allocateTempRegister' call like @allocateTempRegister >>= \r1 -> allocateTempRegister
>>= \r2 -> ...@ would give @r1 == r2 == Rax@, which is not the expected behaviour for register allocation.
-}
allocTempRegister ::
  ( MonadState (InstSelectionState isa) m
  , Isa isa
  , Mov isa (Memory isa) (Register isa)
  , Mov isa (Register isa) (Memory isa)
  ) =>
  m (Register isa, m ())
allocTempRegister = do
  (registers, freeRegister) <- allocTempRegisters 1
  case registers of
    [register] -> pure (register, freeRegister)
    _ -> undefined

{-# ANN mov_vr ("HLint: ignore Use camelCase" :: String) #-}
mov_vr ::
  forall isa m.
  ( Isa isa
  , Mov isa (Register isa) (Register isa)
  , Mov isa (Memory isa) (Register isa)
  , Mov isa Immediate (Register isa)
  , Lea isa (Memory isa) (Register isa)
  , MonadState (InstSelectionState isa) m
  ) =>
  Value isa ->
  Register isa ->
  m ()
mov_vr value dest =
  emit $
    case value of
      ValueAt (Register register) ->
        [mov Op2{src = register, dest} | register /= dest]
      ValueAt (Stack offset) -> do
        [mov Op2{src = Mem{base = BaseRegister $ framePointerRegister @isa, offset}, dest}]
      AddressOf (Metis.InstSelection.Symbol label) ->
        [mov Op2{src = imm label, dest}]
      AddressOf (Memory mem) ->
        [lea Op2{src = mem, dest}]
      Literal lit ->
        [mov Op2{src = imm lit, dest}]

{-# ANN mov_vm ("HLint: ignore Use camelCase" :: String) #-}
mov_vm ::
  forall isa m.
  ( Isa isa
  , Mov isa Immediate (Register isa)
  , Mov isa Immediate (Memory isa)
  , Mov isa (Register isa) (Register isa)
  , Mov isa (Register isa) (Memory isa)
  , Mov isa (Memory isa) (Register isa)
  , Lea isa (Memory isa) (Register isa)
  , MonadState (InstSelectionState isa) m
  ) =>
  Value isa ->
  Memory isa ->
  m ()
mov_vm value dest =
  case value of
    ValueAt (Register register) ->
      emit [mov Op2{src = register, dest}]
    ValueAt Stack{} ->
      inRegister value $ \register ->
        emit [mov Op2{src = register, dest}]
    AddressOf (Metis.InstSelection.Symbol label) ->
      emit [mov Op2{src = imm label, dest}]
    AddressOf Memory{} ->
      inRegister value $ \register ->
        emit [mov Op2{src = register, dest}]
    Literal lit ->
      emit [mov Op2{src = imm lit, dest}]

{-# ANN mov_vl ("HLint: ignore Use camelCase" :: String) #-}
mov_vl ::
  forall isa m.
  ( Isa isa
  , Mov isa Immediate (Register isa)
  , Mov isa Immediate (Memory isa)
  , Mov isa (Register isa) (Register isa)
  , Mov isa (Register isa) (Memory isa)
  , Mov isa (Memory isa) (Register isa)
  , Lea isa (Memory isa) (Register isa)
  , MonadState (InstSelectionState isa) m
  ) =>
  Value isa ->
  Location isa ->
  m ()
mov_vl value dest =
  case dest of
    Register register ->
      mov_vr value register
    Stack offset ->
      mov_vm value Mem{base = BaseRegister $ framePointerRegister @isa, offset}

{- | Moves a value to a register. If the value is already in a register, then nothing
changes. If the value is at a stack address, then the contents at that stack address are moved into
a temporary register.

Nested calls to 'inRegister' are invalid because of the way it spills when no registers are
available. When no registers are available, 'inRegister' picks 'Rax' as the target register. The
contents of 'Rax' are saved to stack memory and restored after the callback. A nested 'inRegister'
call like @inRegister l1 (\r1 -> inRegister l2 (\r2 -> ...))@ would give @r1 == r2 == Rax@, which
is not the expected behaviour for register allocation.
-}
inRegister ::
  forall isa m a.
  ( MonadState (InstSelectionState isa) m
  , Isa isa
  , Mov isa (Register isa) (Register isa)
  , Mov isa (Memory isa) (Register isa)
  , Mov isa (Register isa) (Memory isa)
  , Mov isa Immediate (Register isa)
  , Lea isa (Memory isa) (Register isa)
  ) =>
  Value isa ->
  (Register isa -> m a) ->
  m a
inRegister value f = do
  (register, freeRegister) <-
    case value of
      ValueAt (Register register) ->
        pure (register, pure ())
      ValueAt Stack{} ->
        allocTempRegister
      AddressOf{} ->
        allocTempRegister
      Literal{} ->
        allocTempRegister
  mov_vr value register
  a <- f register
  freeRegister
  pure a

{-
inRegister2 ::
  forall isa m a.
  ( MonadState (InstSelectionState isa) m
  , Isa isa
  , Mov isa (Register isa) (Register isa)
  , Mov isa (Memory isa) (Register isa)
  , Mov isa (Register isa) (Memory isa)
  , Mov isa Immediate (Register isa)
  , Lea isa (Memory isa) (Register isa)
  ) =>
  Value isa ->
  Value isa ->
  (Register isa -> Register isa -> m a) ->
  m a
inRegister2 value1 value2 f = do
  (registers, freeRegister) <-
    case (value1, value2) of
      (ValueAt (Register register1), ValueAt (Register register2)) ->
        pure ([register1, register2], pure ())
      (ValueAt (Register register1), ValueAt Stack{}) -> do
        (register2, free) <- allocTempRegister
        pure ([register1, register2], free)
      (ValueAt (Register register1), AddressOf _) -> do
        (register2, free) <- allocTempRegister
        pure ([register1, register2], free)
      (ValueAt Stack{}, ValueAt (Register register2)) -> do
        (register1, free) <- allocTempRegister
        pure ([register1, register2], free)
      (ValueAt Stack{}, ValueAt Stack{}) ->
        allocTempRegisters 2
      (ValueAt Stack{}, AddressOf _) ->
        allocTempRegisters 2
      (AddressOf _, ValueAt (Register register2)) -> do
        (register1, free) <- allocTempRegister
        pure ([register1, register2], free)
      (AddressOf _, ValueAt Stack{}) ->
        allocTempRegisters 2
      (AddressOf _, AddressOf _) ->
        allocTempRegisters 2
  case registers of
    [register1, register2] -> do
      emit $ mov_vr value1 register1 <> mov_vr value2 register2
      a <- f register1 register2
      freeRegister
      pure a
    _ ->
      undefined
-}

instSelectionStore_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  Anf.Var ->
  -- | Type: @Ptr a@
  Anf.Simple ->
  -- | Type: @a@
  Anf.Simple ->
  m ()
instSelectionStore_X86_64 _var ptr val = do
  ptr' <- instSelectionSimple_X86_64 ptr
  val' <- instSelectionSimple_X86_64 val

  -- TODO: assign `var` to Unit value after
  varKinds <- asks (.varKinds)
  nameTys <- asks (.nameTys)
  varTys <- asks (.varTys)
  case Anf.typeOf varKinds nameTys varTys val of
    Right Type.Var{} ->
      error "TODO: Store/Var"
    Right Type.Unknown ->
      error "impossible: can't store to *Unknown"
    Right Type.Uint64 ->
      case (ptr', val') of
        (ValueAt (Register ptrRegister), Literal lit) -> do
          emit [mov Op2{src = imm lit, dest = Mem{base = BaseRegister ptrRegister, offset = 0}}]
        (ValueAt (Register ptrRegister), _) -> do
          inRegister val' $ \valRegister ->
            emit [mov Op2{src = valRegister, dest = Mem{base = BaseRegister ptrRegister, offset = 0}}]
        (ValueAt (Stack offset), ValueAt (Register valRegister)) ->
          emit [mov Op2{src = valRegister, dest = Mem{base = BaseRegister Rbp, offset}}]
        (ValueAt (Stack offset), ValueAt Stack{}) ->
          inRegister val' $ \valRegister ->
            emit [mov Op2{src = valRegister, dest = Mem{base = BaseRegister Rbp, offset}}]
        (ValueAt (Stack offset), AddressOf{}) ->
          inRegister val' $ \valRegister ->
            emit [mov Op2{src = valRegister, dest = Mem{base = BaseRegister Rbp, offset}}]
        (ValueAt (Stack offset), Literal lit) ->
          emit [mov Op2{src = imm lit, dest = Mem{base = BaseRegister Rbp, offset}}]
        (AddressOf (Metis.InstSelection.Symbol ptrLabel), Literal lit) ->
          emit [mov Op2{src = imm lit, dest = Mem{base = BaseLabel @X86_64 ptrLabel, offset = 0}}]
        (AddressOf (Metis.InstSelection.Symbol ptrLabel), _) ->
          inRegister val' $ \valRegister ->
            emit [mov Op2{src = valRegister, dest = Mem{base = BaseLabel @X86_64 ptrLabel, offset = 0}}]
        (AddressOf (Memory ptrMem), Literal lit) ->
          emit [mov Op2{src = imm lit, dest = ptrMem}]
        (AddressOf (Memory ptrMem), _) ->
          inRegister val' $ \valRegister ->
            emit [mov Op2{src = valRegister, dest = ptrMem}]
        (Literal{}, _) ->
          error "cannot store to literal"
    Right Type.Bool ->
      error "TODO: Store/Bool"
    Right Type.Unit ->
      error "TODO: Store/Unit"
    Right Type.Fn{} -> do
      error "TODO: Store/Fn"
    Right Type.Forall{} -> do
      error "TODO: Store/Forall"
    Right Type.Ptr{} -> do
      error "TODO: Store/Ptr"
    Left kind ->
      error $ "expected type, got kind " <> show kind

instSelectionLoad_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  Anf.Var ->
  -- | Type: @Ptr a@
  Anf.Simple ->
  m ()
instSelectionLoad_X86_64 var ptr = do
  ptr' <- instSelectionSimple_X86_64 ptr

  varTys <- asks (.varTys)
  let ty = varTys var
  case ty of
    Type.Var{} ->
      error "TODO: Load/Var"
    Type.Unknown ->
      error "impossible: can't load from *Unknown"
    Type.Uint64 -> do
      location <- allocLocation $ Type.sizeOf ty
      inRegister ptr' $ \ptrRegister ->
        emit $
          case location of
            Register register ->
              [mov Op2{src = Mem{base = BaseRegister ptrRegister, offset = 0}, dest = register}]
            Stack offset ->
              [ mov Op2{src = Mem{base = BaseRegister ptrRegister, offset = 0}, dest = ptrRegister}
              , mov Op2{src = ptrRegister, dest = Mem{base = BaseRegister Rbp, offset}}
              ]
      modify (\s -> s{locations = HashMap.insert var location s.locations})
    Type.Bool ->
      error "TODO: Load/Bool"
    Type.Unit ->
      error "TODO: Load/Unit"
    Type.Fn{} -> do
      error "TODO: Load/Fn"
    Type.Forall{} -> do
      error "TODO: Load/Forall"
    Type.Ptr{} -> do
      error "TODO: Load/Ptr"

instSelectionGetField_X86_64 ::
  (MonadState (InstSelectionState X86_64) m, MonadReader (InstSelectionEnv X86_64) m, MonadLog m) =>
  Anf.Var ->
  Anf.Simple ->
  Text ->
  m ()
instSelectionGetField_X86_64 var ptr field =
  error "TODO: GetField" var ptr field