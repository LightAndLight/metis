{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Metis.Anf (
  Expr (..),
  Var (..),
  VarInfo (..),
  Simple (..),
  typeOf,
  Compound (..),
  Binop (..),
  ExprInfo (..),
  Function (..),

  -- * Core translation
  fromFunction,
  fromCore,
  fromCoreExpr,

  -- * ANF expression builder
  AnfBuilderT,
  runAnfBuilderT,
  freshLabel,
  freshVar,
  freshTyVar,
  emit,
  letS,
  letC,
) where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad.State.Class (get, gets, modify, put)
import Control.Monad.State.Strict (StateT, lift, runStateT)
import Data.Functor.Identity (runIdentity)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable)
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import Data.Traversable (for)
import Data.Word (Word64)
import qualified Metis.Core as Core
import Metis.Kind (Kind)
import Metis.Literal (Literal)
import qualified Metis.Literal as Literal
import Metis.Type (Type)
import qualified Metis.Type as Type

data Expr
  = Return Simple
  | LetS Var (Type Var) Simple Expr
  | LetC Var (Type Var) Compound Expr
  | IfThenElse Simple Expr Expr Expr
  | Jump Var Simple
  | Label Var Var Expr
  deriving (Show, Eq)

data Simple
  = Var Var
  | Name Text
  | Literal Literal
  | Type (Type Var)
  deriving (Show, Eq)

typeOf :: (Var -> Kind) -> (Text -> Type ty) -> (Var -> Type ty) -> Simple -> Either Kind (Type ty)
typeOf varKinds nameTys varTys simple =
  case simple of
    Var var -> Right $ varTys var
    Name name -> Right $ nameTys name
    Literal lit -> Right $ Literal.typeOf lit
    Type ty -> Left $ Type.kindOf varKinds ty

data Compound
  = Binop Binop Simple Simple
  | Call Simple [Simple]
  | Alloca (Type Var)
  | Store Simple Simple
  | Load Simple
  deriving (Show, Eq)

data Binop = Add | Subtract
  deriving (Show, Eq)

data ExprInfo = ExprInfo
  { labelArgs :: HashMap Var Var
  , varKinds :: HashMap Var Kind
  , varTys :: HashMap Var (Type Var)
  }
  deriving (Eq, Show)

data Function = Function
  { name :: Text
  , tyArgs :: [(Var, Kind)]
  , args :: [(Var, Type Var)]
  , retTy :: Type Var
  , bodyInfo :: ExprInfo
  , body :: Expr
  }
  deriving (Eq, Show)

data AnfBuilderState = AnfBuilderState
  { nextVar :: Word64
  , program :: Expr -> Expr
  , labelArgs :: HashMap Var Var
  , varKinds :: HashMap Var Kind
  , varTys :: HashMap Var (Type Var)
  }

newtype AnfBuilderT m a = AnfBuilderT {value :: StateT AnfBuilderState m a}
  deriving (Functor, Applicative, Monad)

runAnfBuilderT :: (Monad m) => AnfBuilderT m a -> m (AnfBuilderState, a)
runAnfBuilderT ma = do
  (a, s) <-
    runStateT
      ma.value
      AnfBuilderState
        { nextVar = 0
        , program = id
        , labelArgs = mempty
        , varKinds = mempty
        , varTys = mempty
        }
  pure (s, a)

newtype Var = MkVar {value :: Word64}
  deriving (Show, Eq, Hashable)

freshLabel :: (Monad m) => AnfBuilderT m Var
freshLabel =
  AnfBuilderT $ do
    n <- gets (.nextVar)
    let var = MkVar n
    modify (\s -> s{nextVar = n + 1})
    pure var

freshVar :: (Monad m) => Type Var -> AnfBuilderT m Var
freshVar ty =
  AnfBuilderT $ do
    n <- gets (.nextVar)
    let var = MkVar n
    modify (\s -> s{nextVar = n + 1, varTys = HashMap.insert var ty s.varTys})
    pure var

freshTyVar :: (Monad m) => Kind -> AnfBuilderT m Var
freshTyVar kind =
  AnfBuilderT $ do
    n <- gets (.nextVar)
    let var = MkVar n
    modify (\s -> s{nextVar = n + 1, varKinds = HashMap.insert var kind s.varKinds})
    pure var

emit :: (Monad m) => (Expr -> Expr) -> AnfBuilderT m ()
emit f = AnfBuilderT $ modify (\s -> s{program = s.program . f})

data VarInfo = VarInfo {size :: Word64}
  deriving (Show, Eq)

letS :: (Monad m) => Type Var -> Simple -> AnfBuilderT m Var
letS ty value = do
  var <- freshVar ty
  emit $ LetS var ty value
  pure var

letC :: (Monad m) => Type Var -> Compound -> AnfBuilderT m Var
letC ty value = do
  var <- freshVar ty
  emit $ LetC var ty value
  pure var

block :: (Monad m) => Var -> Var -> AnfBuilderT m ()
block label arg = do
  emit $ Label label arg
  AnfBuilderT $ modify (\s -> (s :: AnfBuilderState){labelArgs = HashMap.insert label arg s.labelArgs})

programOf :: (Monad m) => AnfBuilderT m a -> AnfBuilderT m (Expr -> Expr, a)
programOf ma =
  AnfBuilderT $ do
    s <- get
    (a, s') <- lift $ runStateT ma.value s{program = id}
    put s'{program = s.program}
    pure (s'.program, a)

fromCore :: (Text -> Type Var) -> (ty -> Var) -> (tm -> Var) -> Core.Expr ty tm -> (ExprInfo, Expr)
fromCore nameTys toTyVar toVar expr =
  ( ExprInfo
      { labelArgs = s.labelArgs
      , varKinds = s.varKinds
      , varTys = s.varTys
      }
  , s.program (Return simple)
  )
  where
    (s, simple) = runIdentity . runAnfBuilderT $ fromCoreExpr nameTys toTyVar toVar expr

fromFunction :: (Text -> Type Var) -> Core.Function -> Function
fromFunction nameTys Core.Function{name, tyArgs, args, retTy, body} =
  Function
    { name
    , tyArgs = tyArgs'
    , args = args'
    , retTy = retTy'
    , bodyInfo = ExprInfo{labelArgs, varKinds, varTys}
    , body = program (Return simple)
    }
  where
    (AnfBuilderState{labelArgs, varKinds, varTys, program}, (tyArgs', args', retTy', simple)) =
      runIdentity . runAnfBuilderT $ do
        tyVars <- traverse (\(_, kind) -> freshTyVar kind) tyArgs
        let renameTyVar index = tyVars !! fromIntegral @Word64 @Int index
        args'' <- traverse (\(_, ty) -> let ty' = fmap renameTyVar ty in (,) <$> freshVar ty' <*> pure ty') args
        body' <- fromCoreExpr nameTys renameTyVar (\index -> fst $ args'' !! fromIntegral @Word64 @Int index) body
        pure
          ( zipWith (\tyVar (_, kind) -> (tyVar, kind)) tyVars tyArgs
          , args''
          , fmap renameTyVar retTy
          , body'
          )

fromCoreExpr ::
  (Monad m) =>
  (Text -> Type Var) ->
  (ty -> Var) ->
  (tm -> Var) ->
  Core.Expr ty tm ->
  AnfBuilderT m Simple
fromCoreExpr nameTys toTyVar toVar expr =
  case expr of
    Core.Var var ->
      pure $ Var (toVar var)
    Core.Name name ->
      pure $ Name name
    Core.Literal lit ->
      pure $ Literal lit
    Core.Add ty a b -> do
      a' <- fromCoreExpr nameTys toTyVar toVar a
      b' <- fromCoreExpr nameTys toTyVar toVar b
      Var <$> letC (fmap toTyVar ty) (Binop Add a' b')
    Core.Subtract ty a b -> do
      a' <- fromCoreExpr nameTys toTyVar toVar a
      b' <- fromCoreExpr nameTys toTyVar toVar b
      Var <$> letC (fmap toTyVar ty) (Binop Subtract a' b')
    Core.Let _ _ valueTy value rest -> do
      value' <- fromCoreExpr nameTys toTyVar toVar value
      var <-
        case value' of
          Var var ->
            pure var
          Name{} ->
            letS (fmap toTyVar valueTy) value'
          Literal{} ->
            letS (fmap toTyVar valueTy) value'
          Type{} ->
            letS (fmap toTyVar valueTy) value'
      fromCoreExpr nameTys toTyVar (unvar (\() -> var) toVar) (fromScope rest)
    Core.IfThenElse ty cond then_ else_ -> do
      cond' <- fromCoreExpr nameTys toTyVar toVar cond
      (then_', thenSimple) <- programOf $ fromCoreExpr nameTys toTyVar toVar then_
      (else_', elseSimple) <- programOf $ fromCoreExpr nameTys toTyVar toVar else_
      label <- freshLabel
      emit $ IfThenElse cond' (then_' $ Jump label thenSimple) (else_' $ Jump label elseSimple)

      arg <- freshVar $ fmap toTyVar ty
      block label arg
      pure $ Var arg
    Core.Call ty function tyArgs args -> do
      let ty' = fmap toTyVar ty
      function' <- fromCoreExpr nameTys toTyVar toVar function
      let tyArgs' = fmap (fmap toTyVar) tyArgs
      args' <- traverse (fromCoreExpr nameTys toTyVar toVar) args

      varKinds <-
        AnfBuilderT $
          gets
            ( \s var ->
                Maybe.fromMaybe
                  (error $ "var " <> show var <> " missing from var kinds map")
                  (HashMap.lookup var s.varKinds)
            )
      varTys <-
        AnfBuilderT $
          gets
            ( \s var ->
                Maybe.fromMaybe
                  (error $ "var " <> show var <> " missing from var types map")
                  (HashMap.lookup var s.varTys)
            )
      let functionTy =
            either
              (\kind -> error $ "expected type, got kind " <> show kind)
              id
              (typeOf varKinds nameTys varTys function')
      let (_tyVarsKinds, instantiatedArgTys, instantiatedRetTy) = instantiateFunctionType Type.Var functionTy tyArgs'
      let (argTysPolymorphism, retTyPolymorphism) = getFunctionPolymorphism functionTy

      args'' <-
        for (zip3 instantiatedArgTys argTysPolymorphism args') $ \(instantiatedArgTy, argTyPolymorphism, arg) ->
          case (instantiatedArgTy, argTyPolymorphism) of
            (Type.Var{}, Poly) ->
              pure arg
            (_, Mono) ->
              pure arg
            (_, Poly) -> do
              allocaResult <- Var <$> letC (Type.Ptr instantiatedArgTy) (Alloca instantiatedArgTy)
              _ <- letC Type.Unit (Store allocaResult arg)
              pure allocaResult
      case (instantiatedRetTy, retTyPolymorphism) of
        (Type.Var{}, Poly) ->
          Var <$> letC ty' (Call function' (fmap Type tyArgs' <> args''))
        (_, Mono) ->
          Var <$> letC ty' (Call function' (fmap Type tyArgs' <> args''))
        (_, Poly) -> do
          callResult <- letC (Type.Ptr ty') (Call function' (fmap Type tyArgs' <> args''))
          Var <$> letC ty' (Load $ Var callResult)
  where
    instantiateFunctionType :: (ty -> Type Var) -> Type ty -> [Type Var] -> ([(Text, Kind)], [Type Var], Type Var)
    instantiateFunctionType subst ty tyArgs =
      case ty of
        Type.Fn args ret ->
          ([], fmap (>>= subst) args, ret >>= subst)
        Type.Forall tyArgKinds body ->
          let tyArgCount = length tyArgKinds
              (usedTyArgs, tyArgs') = splitAt tyArgCount tyArgs
              (tyArgKinds', args', ret) =
                instantiateFunctionType
                  (unvar (\index -> usedTyArgs !! fromIntegral @Word64 @Int index) subst)
                  (fromScope body)
                  tyArgs'
           in (tyArgKinds <> tyArgKinds', args', ret)
        _ ->
          case tyArgs of
            [] -> ([], [], ty >>= subst)
            _ -> error "too many type arguments"

    getFunctionPolymorphism :: Type ty -> ([Polymorphism], Polymorphism)
    getFunctionPolymorphism ty =
      case ty of
        Type.Fn args ret ->
          (fmap getTypePolymorphism args, getTypePolymorphism ret)
        Type.Forall _tyArgKinds body ->
          getFunctionPolymorphism (fromScope body)
        _ ->
          ([], getTypePolymorphism ty)

    getTypePolymorphism :: Type ty -> Polymorphism
    getTypePolymorphism ty =
      case ty of
        Type.Var{} -> Poly
        Type.Uint64 -> Mono
        Type.Bool -> Mono
        Type.Unit -> Mono
        Type.Fn{} -> Mono
        Type.Forall{} -> Mono
        Type.Ptr{} -> Mono

data Polymorphism = Poly | Mono