
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


module Zilly.Classic.TypeCheck where


import Parser.Classic.ZillyParser qualified as P
import Utilities.LensM
import Utilities.TypedMap hiding (empty)
import Utilities.ShowM
import Zilly.ADT.Expression
import Zilly.ADT.Action
import Zilly.Classic.Action
import Zilly.Classic.Expression
import Zilly.Classic.Interpreter hiding (Env)
import Zilly.RValue
import Zilly.Types
import Zilly.Upcast
import Control.Monad.Reader


import Data.Kind (Type)
import Data.Singletons
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (Alternative(..))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Writer.CPS
import Control.Monad.Error.Class
import Control.Monad.Trans.Maybe
import Parser.Classic.ZillyParser qualified as P
import Control.Monad (MonadPlus(mzero))
import Text.Parsec (SourcePos)
import Data.Singletons.Decide
import Data.Traversable


type Some :: forall k. (k -> Type) -> Type 
data Some (f :: k -> Type) where
    MkSome :: forall {k} f (a :: k). SingI a => f a -> Some f

type TypeCheckEnv = Map Symbol Types
type ErrorLog = [TypeCheckErrors]

newtype ExpectedType = ExpectedType Types deriving newtype Show
newtype GotType      = GotType      Types deriving newtype Show

data TypeCheckErrors 
  = SymbolNotDefined Symbol SourcePos
  | FormulaNeedsLValue P.Expr SourcePos
  | TypeMismatch ExpectedType GotType SourcePos
  | NonUnifiableTypes (Types,SourcePos) (Types,SourcePos)
  | ArgNotSubtype    (Types,SourcePos) Types
  | ArgIsNotStrictSubtype   (Types,SourcePos) Types
  | AppNotAFun Types SourcePos
  | RHSNotSubtype    (Types,SourcePos) Types
  | RHSIsNotStrictSubtype   (Types,SourcePos) Types

instance Show TypeCheckErrors where
  show (SymbolNotDefined s pos) = "Symbol " <> show s <> " not defined " <> show pos
  show (FormulaNeedsLValue e pos) = "Needs lvalue " <> show e <> " " <> show pos 
  show (TypeMismatch t1 t2 pos) = "Type mismatch " <> show pos
  show (NonUnifiableTypes (t1,pos1) (t2,pos2) ) 
    = "Non unifiable types:\n" 
      <> show t1 <> "(" <> show pos1 <> ")\n" 
      <> show t2 <> "(" <> show pos2 <> ")\n" 
  show (ArgNotSubtype (t,s) expected) 
    = "Value passed as argument is not a subtype of the argument.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (ArgIsNotStrictSubtype (t,s) expected) 
    = "Value passed as argument is not a strict subtype of the argument.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (AppNotAFun t s) 
    = "Left argument of function application is not a function. Expected type: " <> show t <> " " <> show s
  show (RHSNotSubtype (t,s) expected) 
    = "Right hand side of assignment is not a subtype of the left hand side.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (RHSIsNotStrictSubtype (t,s) expected) 
    = "Right hand side of assignment is not a strict subtype of the left hand side.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s


newtype TCM a = TCM { unTCM :: ReaderT TypeCheckEnv (MaybeT (Writer ErrorLog) ) a }
  deriving newtype 
    ( Functor
    , Applicative
    , Monad
    , MonadReader TypeCheckEnv
    , MonadWriter ErrorLog
    , Alternative
    , MonadFail
    )

data TcGen  = TcGen
  { tcGenEnv :: TypeCheckEnv
  , tcGenPos :: SourcePos
  }


class TypeCheck actx e ret | e -> ret where
  type TCC actx ret :: ret -> Type
  type TCReturn actx e :: Type 
  typeCheck :: forall {f} {ctx}.
    ( AssocActionTag actx ~ ctx
    , TCC actx ret ~ f
    ) => e -> TCM (Some f,TCReturn actx e)

instance TypeCheck ActionTag P.Atom Types where
  type TCC ActionTag  Types = E ExprTag
  type TCReturn ActionTag P.Atom = TcGen
  typeCheck (P.Val s pos) = do
    env <- ask
    pure (MkSome $  ValE s,TcGen env pos)
  typeCheck (P.Var s pos) = do
    env <- ask
    case M.lookup s env of
      Just t -> case toSing  t of
        SomeSing @_ @t st -> withSingI st 
          $ pure (MkSome $ VarE (mkVar @t @ExprTag s) ,TcGen env pos)
      Nothing -> 
        tell [SymbolNotDefined s pos] >> empty
  typeCheck (P.Parens e _) = typeCheck @ActionTag e
  typeCheck (P.Defer e pos) = do
    (MkSome @_ @a a,tcGen) <- typeCheck @ActionTag e
    withSingIRType @a
      $ withRVType @ExprTag (sing @a)
      $ pure (MkSome $ DeferE a,tcGen{tcGenPos=pos})
  typeCheck (P.IfThenElse e1 e2 e3 pos) = do
    env <- ask
    (MkSome @_ @x0 x0,e0r) <- typeCheck @ActionTag e1
    (MkSome @_ @x1 x1,e1r) <- typeCheck @ActionTag e2
    (MkSome @_ @x2 x2,e2r) <- typeCheck @ActionTag e3
    withSingIRType @x0 
      $ withSingIRType @x1
      $ withSingIRType @x2
      $ withRVType @ExprTag (sing @x0)
      $ withRVType @ExprTag (sing @x1)
      $ withRVType @ExprTag (sing @x2)
      $ case decideEquality (sing @(RValueT x0)) (sing @(Value Z)) of
        Nothing -> tell [TypeMismatch (ExpectedType $ Value Z)  (GotType $ demote @x0) $ tcGenPos e0r] >> empty
        Just Refl -> case upcastable @(RValueT x1) @(RValueT x2) @ExprTag of
          NonExistentUB     ->  tell 
            [NonUnifiableTypes (demote @x1,tcGenPos e1r) (demote @x2,tcGenPos e2r) ] 
            >> empty
          SameTypeUB _      -> pure (MkSome $ IfE x0 x1 x2,TcGen env pos)
          LeftUB _          -> pure (MkSome $ IfE x0 x1 x2,TcGen env pos)
          RightUB _         -> pure (MkSome $ IfE x0 x1 x2,TcGen env pos)
          SomethingElseUB _ -> pure (MkSome $ IfE x0 x1 x2,TcGen env pos)
  typeCheck (P.Lambda s t e pos) = do
    env <- ask
    let env' = M.insert s (P.parserT2AdtT t) env
    (MkSome @_ @body body,_) <- local (const env') $ typeCheck @ActionTag e
    -- never fails
    (MkSome @_ @var (Var _ var),_) <- local (const env') $ typeCheck @ActionTag (P.Var s pos)
    withRVType @ExprTag (sing @body)
      $ pure (MkSome $ LambdaE var body,TcGen env pos)


instance TypeCheck ActionTag P.Term Types where
  type TCC ActionTag Types = E ExprTag
  type TCReturn ActionTag P.Term = TcGen
  typeCheck (P.OfAtom a) = typeCheck @ActionTag a
  typeCheck (P.App f x pos) = do
    (MkSome @_ @f' f',fr) <- typeCheck @ActionTag f
    (MkSome @_ @x' x',xr) <- typeCheck @ActionTag x
    withRVType @ExprTag (sing @f')
      $ withRVType @ExprTag (sing @x')
      $ withSingIRType @f'
      $ withSingIRType @x'
      $ case sing @f' of
        SValue ((sarg :: Sing arg) :%-> (sb :: Sing b)) 
          -> withSingI sarg 
          $ withSingI sb
          $ case upcastable @(RValueT x') @arg  @ExprTag of
            NonExistentUB     -> tell 
              [ ArgNotSubtype (demote @(RValueT x'), tcGenPos xr) (demote @arg)] 
              >> pure (MkSome @_ @b $ ExpE bottom, TcGen M.empty pos)
            SomethingElseUB _ -> tell 
              [ArgIsNotStrictSubtype (demote @(RValueT x'), tcGenPos xr) (demote @arg)] 
              >> pure (MkSome @_ @b $ ExpE bottom, TcGen M.empty pos)
            LeftUB _          -> tell 
              [ArgNotSubtype (demote @(RValueT x'), tcGenPos xr) (demote @arg)] 
              >> pure (MkSome @_ @b $ ExpE bottom, TcGen M.empty pos)
            SameTypeUB _      -> pure (MkSome $ AppE f' x',TcGen M.empty pos)
            RightUB _         -> pure (MkSome $ AppE f' x',TcGen M.empty pos)
            
        _ -> tell [AppNotAFun (demote @f') $ tcGenPos fr] >> empty
      

instance TypeCheck ActionTag P.Expr Types where
  type TCC ActionTag  Types = E ExprTag
  type TCReturn ActionTag P.Expr = TcGen
  typeCheck (P.OfTerm t) = typeCheck @ActionTag t
  typeCheck (P.Minus e t pos) = do
    env <- ask
    (MkSome @_ @e' e',er) <- typeCheck @ActionTag e
    (MkSome @_ @t' t',tr) <- typeCheck @ActionTag t
    withRVType @ExprTag (sing @e')
      $ withRVType @ExprTag (sing @t')
      $ withSingIRType @e'
      $ withSingIRType @t'
      $ case (decideEquality' @_ @(RValueT e') @(Value Z),decideEquality' @_ @(RValueT t') @(Value Z)) of
        (Just Refl,Just Refl) -> pure (MkSome $ MinusE e' t',TcGen env pos)
        (Nothing,Nothing) 
            -> tell 
              [ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT e')) $ tcGenPos er
              , TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT t')) $ tcGenPos tr
              ] 
            >> pure (MkSome @_ @(Value Z) $ ExpE bottom, TcGen M.empty pos)
        (Just Refl,Nothing) 
          -> tell [TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT t')) $ tcGenPos tr] 
            >> pure (MkSome @_ @(Value Z) $ ExpE bottom, TcGen M.empty pos)
        (Nothing,Just Refl) 
          -> tell [TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT e')) $ tcGenPos er] 
            >> pure (MkSome @_ @(Value Z) $ ExpE bottom, TcGen M.empty pos)
  typeCheck (P.Less e t pos) = do
    env <- ask
    (MkSome @_ @e' e',er) <- typeCheck @ActionTag e
    (MkSome @_ @t' t',tr) <- typeCheck @ActionTag t
    withRVType @ExprTag (sing @e')
      $ withRVType @ExprTag (sing @t')
      $ withSingIRType @e'
      $ withSingIRType @t'
      $ case (decideEquality' @_ @(RValueT e') @(Value Z),decideEquality' @_ @(RValueT t') @(Value Z)) of
        (Just Refl,Just Refl) -> pure (MkSome $ LessE e' t',TcGen env pos)
        (Nothing,Nothing) 
            -> tell 
              [ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT e')) $ tcGenPos er
              , TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT t')) $ tcGenPos tr
              ] 
            >> pure (MkSome @_ @(Value Z) $ ExpE bottom, TcGen M.empty pos)
        (Just Refl,Nothing) 
          -> tell [TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT t')) $ tcGenPos tr] 
            >> pure (MkSome @_ @(Value Z) $ ExpE bottom, TcGen M.empty pos)
        (Nothing,Just Refl) 
          -> tell [TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @(RValueT e')) $ tcGenPos er] 
            >> pure (MkSome @_ @(Value Z) $ ExpE bottom, TcGen M.empty pos)

instance TypeCheck ActionTag P.A0 () where
  type TCC ActionTag () = A ActionTag
  type TCReturn ActionTag P.A0 = TcGen
  -- typeCheck (P.Decl t s e pos) = do
  --   env <- ask
  --   let env' = M.insert s (rValueT $ P.parserT2AdtT t) env
  --   (MkSome @_ @e' e',er) <- local (const env') $ typeCheck @ActionTag e
  --   -- never fails
  --   (MkSome @_ @var (Var _ var),_) <- local (const env') $ typeCheck @ActionTag (P.Var s pos)
  --   withSingIRType @e'
  --     $ withSingIRType @var
  --     $ withRVType @ExprTag (sing @e')
  --     $ withRVType @ExprTag (sing @var)
  --     $ case upcastable @var  @e' @ExprTag of
  --       SameTypeUB  _     -> pure (MkSome (var := e'),TcGen env' pos)
  --       LeftUB      _     -> pure (MkSome (var := e'),TcGen env' pos)
  --       RightUB     _     
  --         -> tell [RHSNotSubtype    (demote @e', tcGenPos er) $ demote @var] 
  --           >> pure  (MkSome $ OfExpr @_ @(Value Z) (ExpE bottom),TcGen env' pos)
  --       SomethingElseUB _ 
  --         -> tell [RHSIsNotStrictSubtype    (demote @e', tcGenPos er) $ demote @var] 
  --           >> pure  (MkSome $ OfExpr @_ @(Value Z) (ExpE bottom),TcGen env' pos)
  --       NonExistentUB
  --         -> tell [RHSNotSubtype    (demote @e', tcGenPos er) $ demote @var] 
  --           >> pure  (MkSome $ OfExpr @_ @(Value Z) (ExpE bottom),TcGen env' pos)
  --
  -- typeCheck (P.Assign s e pos) = do
  --   env <- ask
  --   (MkSome @_ @e' e',er) <- typeCheck @ActionTag e
  --   -- never fails
  --   (MkSome @_ @var (Var _ var),_) <- typeCheck @ActionTag (P.Var s pos)
  --   withSingIRType @e'
  --     $ withSingIRType @var
  --     $ withRVType @ExprTag (sing @e')
  --     $ withRVType @ExprTag (sing @var)
  --     $ case upcastable @var  @e' @ExprTag of
  --       SameTypeUB  _     -> pure (MkSome (var :=. e'),TcGen env pos)
  --       LeftUB      _     -> pure (MkSome (var :=. e'),TcGen env pos)
  --       RightUB     _     
  --         -> tell [RHSNotSubtype    (demote @e', tcGenPos er) $ demote @var] 
  --           >> pure  (MkSome $ OfExpr @_ @(Value Z) (ExpE bottom),TcGen env pos)
  --       SomethingElseUB _ 
  --         -> tell [RHSIsNotStrictSubtype    (demote @e', tcGenPos er) $ demote @var] 
  --           >> pure  (MkSome $ OfExpr @_ @(Value Z) (ExpE bottom),TcGen env pos)
  --       NonExistentUB
  --         -> tell [RHSNotSubtype    (demote @e', tcGenPos er) $ demote @var] 
  --           >> pure  (MkSome $ OfExpr @_ @(Value Z) (ExpE bottom),TcGen env pos)
  typeCheck (P.Print e pos) = do
    env <- ask
    (MkSome @_ @e' e',_) <- typeCheck @ActionTag e
    withRVType @ExprTag (sing @e')
      $ pure (MkSome $ Print e',TcGen env pos)

typeCheckProgram :: Map Symbol Types -> P.A1 -> TCM (Map Symbol Types,[A ActionTag '()])
typeCheckProgram ienv as = forAccumM ienv (f as) $ \env a -> do
  (MkSome @_ @a' a',r) <- local (const env) $  typeCheck @ActionTag a
  case decideEquality (sing @a') (sing @'()) of
    Just Refl -> pure (tcGenEnv r,a')
    _ -> tell [undefined] >> empty
  
  where 
    f (P.OfA0 a) = [a]
    f (P.Seq a as) = a : as

typeCheckProgram' :: Map Symbol Types -> P.A1 ->  (Map Symbol Types, Maybe [A ActionTag '()],ErrorLog)
typeCheckProgram' gamma as = case runWriter . runMaybeT . runReaderT (unTCM $ typeCheckProgram gamma as) $ gamma of
  (Just (gamma',as'),elog) -> (gamma',Just as',elog)
  (Nothing,elog)           -> (gamma,Nothing,elog)
