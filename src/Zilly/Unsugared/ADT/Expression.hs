{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Zilly.ADT.Expression
Description : Main Expression Tree a la Trees that grow for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Check
@@
@article{najd2016trees,
  title={Trees that grow},
  author={Najd, Shayan and Jones, Simon Peyton},
  journal={arXiv preprint arXiv:1610.04799},
  year={2016}
}
@@
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf

-}
module Zilly.Unsugared.ADT.Expression where

import Zilly.Unsugared.Newtypes
import Zilly.Unsugared.Environment.TypedMap
import Data.Kind (Type, Constraint)
import Data.Coerce 
import Control.Applicative 
import Prelude.Singletons (SingI(..))
import Control.Monad.IO.Class 
import Control.Monad.Reader
import Data.Singletons.Decide
-- import System.Random.Stateful (globalStdGen, uniformRM)
import Data.Eq.Singletons
import Prelude.Singletons --(SMaybe(..), withSingI, demote, SomeSing(..))
import Debug.Trace (trace)
import Control.Monad.Random 
import GHC.TypeLits

type Effects m = 
  ( Functor m 
  , Applicative m 
  , Monad m
  , Alternative m
  , MonadIO m
  , MonadReader (TypeRepMap (E m)) m
  , EvalMonad (E m) ~ m
  , MonadFail m
  , MonadRandom m
  ) 

type instance EvalMonad (E m) = m

{-| Zilly expression Language. |-}
data  E  (m :: Type -> Type) (a :: PTypes) where
  Val      :: Int -> E m PZ
  Var      :: SingI ltype => LensM (E m) ltype -> E m (Ftype ltype)
  Minus    :: E m PZ -> E m PZ  -> E m PZ
  Less     :: E m PZ -> E m PZ  -> E m PZ
  If       :: SingI x => E m PZ -> E m x          -> E m x -> E m x
  -- 'a' is the type of the expression before rvalue
  -- that is: /. (x : Lazy Int) => x + 1
  Lambda   :: (SingI ltype, SingI b) => LensM (E m) ltype  -> E m b  -> E m (ltype --> b)
  Defer    :: SingI a => E m a -> E m (PLazy a)
  Formula  :: SingI ltype => LensM (E m) ltype -> E m ltype
  Random   :: E m PZ -> E m PZ 
  App      :: forall ltype  b m.
    ( SingI ltype
    , SingI b
    
    ) 
    => E m (ltype --> b) 
    -> E m ltype 
    -> E m b
  LambdaC  :: (SingI ltype, SingI b) 
    => TypeRepMap (E m) -> LensM (E m) ltype -> E m b -> E m (ltype --> b)
  LazyC    :: SingI a => TypeRepMap (E m) -> E m a -> E m a
  Subtyped :: forall sup sub m. 
    ( SingI sup
    , SingI sub
    , (UpperBound sup sub == Just sup) ~ True 
    ) => E m sub -> E m sup 
  MkTuple :: (SingI a, SingI b) => E m a -> E m b -> E m (PTuple a b)
  FstT  :: (SingI a, SingI b) => E m (PTuple a b) -> E m a
  SndT  :: (SingI a, SingI b) => E m (PTuple a b) -> E m b

  Bottom   :: EvalError -> [EvalError] -> E m PTop


data SomeExpression (m :: Type -> Type) where 
  MkSomeExpression :: SingI a => E m a -> SomeExpression m

data EvalError
  = FromGammaError GammaErrors
  | CustomError String

unsafeCoerceExpression :: forall a m. SingI a => SomeExpression m -> E m a 
unsafeCoerceExpression (MkSomeExpression @a' e) = case decideEquality (sing @a) (sing @a') of
  Just Refl -> e
  Nothing -> error $ "Error at unsafeCoerceExpression. Expected type: " 
    <> withShow @a <> " but instead got: " <> withShow @a' 

evalE :: forall a m. (SingI a, Effects m) => E m a -> m (SomeExpression m)
evalE e@(Val {})  = pure $ MkSomeExpression e
evalE  (Var l )   = ask >>= getL l >>= \case 
  Left e -> pure . MkSomeExpression . flip Bottom [] . FromGammaError $ e
  Right a -> evalE a
evalE (Minus l r) = do 
  MkSomeExpression ml' <-  evalE l
  MkSomeExpression mr' <-  evalE r 
  case (ml',mr') of 
    (Val l', Val r') -> pure . MkSomeExpression . Val $ l' - r'
    (Bottom e0 es, Bottom e1 es') -> pure . MkSomeExpression $ Bottom e0 (e1 : es <> es')
    (Bottom e0 es, _)             -> pure . MkSomeExpression $ Bottom e0 es
    (_, Bottom e1 es')            -> pure . MkSomeExpression $ Bottom e1 es'
    _ -> error "Error on evaling '-'-expression. Integer values can only be values or bottom after reduction."
evalE (Less l r) = do 
  MkSomeExpression ml' <-  evalE l
  MkSomeExpression mr' <-  evalE r 
  case (ml',mr') of 
    (Val l', Val r') -> pure . MkSomeExpression . Val . rConnector $ l' < r'
    (Bottom e0 es, Bottom e1 es') -> pure . MkSomeExpression $ Bottom e0 (e1 : es <> es')
    (Bottom e0 es, _)             -> pure . MkSomeExpression $ Bottom e0 es
    (_, Bottom e1 es')            -> pure . MkSomeExpression $ Bottom e1 es'
    _ -> error "Error on evaling '<'-expression. Integer values can only be values or bottom after reduction."
evalE (If c a b) = do 
  MkSomeExpression mc' <- evalE c
  case mc' of 
    Bottom e0 es -> pure . MkSomeExpression $ Bottom e0 es
    Val c' ->
      case connector c' of 
        True  -> evalE a  
        False -> evalE b
    _ -> error "Error on evaling 'if'-expression. Integer values can only be values or bottom after reduction."
evalE (Lambda @arg @body arg body) 
  = (\env -> MkSomeExpression $ LambdaC @arg @body env arg body) <$> ask 
evalE (Defer a)   = ask >>= pure . MkSomeExpression . flip LazyC a
evalE (Formula @ltype x) =  ask >>= viewM x >>= \case 
  Left e ->  pure . MkSomeExpression . flip Bottom [] . FromGammaError $ e 
  Right a 
    -> withSingIFtype @ltype 
    $ ftypeIsSubtype @ltype 
    $ (pure . MkSomeExpression ) a
evalE (Random e) = do 
  MkSomeExpression me' <- evalE e
  case me' of 
    Bottom e0 es   -> pure . MkSomeExpression $ Bottom e0 es
    Val e' | e' < 1 -> pure . MkSomeExpression $ Val 0
    Val e' -> randInt e' >>= pure . MkSomeExpression . Val
    -- Val e'         -> uniformRM (0,e') globalStdGen >>= pure . MkSomeExpression . Val
    _ -> error "Error on evaling 'random' expression. Integer values can only be values or bottom after reduction."
evalE (App @ltype f x) = do
  MkSomeExpression mf0' <- evalE f  
  MkSomeExpression mf'  <- evalE mf0'
  MkSomeExpression @mx' mx' <- evalE x
  case (mf',mx') of
    (Bottom e0 es, Bottom e1 es') -> pure . MkSomeExpression $ Bottom e0 (e1 : es <> es')
    (Bottom e0 es, _)             -> pure . MkSomeExpression $ Bottom e0 es
    (_, Bottom e1 es')            -> pure . MkSomeExpression $ Bottom e1 es'
    (LambdaC @arg env binded body,_) 
      -> withSingIFtype @arg 
      $ case upcastable @(Ftype arg) @mx' of
        SameTypeUB _ -> setFL binded env mx' >>= \case 
          Left e     -> pure . MkSomeExpression . flip Bottom [] . FromGammaError $ e
          Right env' -> local (const env') $ evalE body 
        LeftUB _ 
          -> eqWeakening @(UpperBound (Ftype arg) mx') @(Just (Ftype arg) )
          $ setFL binded env (Subtyped @(Ftype arg) mx') >>= \case 
          Left e     -> pure . MkSomeExpression . flip Bottom [] . FromGammaError $ e
          Right env' -> local (const env') $ evalE body 
        _ -> error "Error on evaling 'function application'-expression. Argument type does not match that of the call."

    (Subtyped @sup @sub f',_) -> case sing @sup of 
      -- SValue ((:%->) @arg @b arg b ) 
      STCon n (SCons @_ @arg arg (SCons @_ @b b SNil))
        -> withKnownSymbol n $ case sameSymbol n (SSymbol @"->") of
          Just Refl -> let 
            aux :: forall arg' body'. (sub ~ (arg' --> body'), SingI arg', SingI body') => m (SomeExpression m)
            aux = case upcastable @arg' @ltype of 
              SameTypeUB _ -> evalE $ App f' x
              LeftUB _     
                -> eqWeakening @(UpperBound arg' ltype) @(Just arg') 
                $ evalE 
                $ App f' (Subtyped @arg' x)
              _ -> error "Error on evaling 'function application'-expression. Subtyped function isnt compatible with applied argument."
            in  withSingI arg 
            $ withSingI b 
            $ withSingIFtype @arg  
            $ ubPreservesFunctionForm' @sup @sub @sup @arg @b 
            $ aux 
          _ -> error "Error on evaling 'function application'-expression. Subtyped functions must be functions themselves."

      _ -> error "Error on evaling 'function application'-expression. Subtyped functions must be functions themselves."
    _ -> error "Error on evaling 'function application'-expression. Function values can only be closures, subtyped functions, or bottom after reduction."
evalE f@(LambdaC {}) = pure . MkSomeExpression $ f
evalE (LazyC env e)  = local (const env) $ evalE e
evalE b@(Bottom {})  = pure . MkSomeExpression $ b
evalE (Subtyped @sup @sub e) = do 
  MkSomeExpression @e' e' <- evalE e 
  withSingIFtype @sup 
    $ withSingIFtype @sub
    $ withSingIUBType @sup @sub
    $ case decideEquality (sing @(e')) (sing @(Ftype sub)) of 
      Nothing -> error "Eror on evaling 'subtyped'-expression. Non matching types"
      Just Refl -> case sing @(UpperBound sup sub) of
        SJust @_ @sx sx 
          -> ftypeRespectsUpperBound @sup @sub  
          $ withSingI sx
          $ ftypeRespectsEquality @(sx) @(sup)
          $ case sing @(Ftype sup) of
            STCon n SNil -> withKnownSymbol n $ case sameSymbol n (SSymbol @"Z") of
              Just Refl -> (pure . MkSomeExpression $ e')
              _ -> (pure . MkSomeExpression . Subtyped @(Ftype sup) @(Ftype sub)) e'
            _ -> (pure . MkSomeExpression . Subtyped @(Ftype sup) @(Ftype sub)) e'
evalE (MkTuple a b) = do 
  MkSomeExpression a' <- evalE a
  MkSomeExpression b' <- evalE b 
  pure . MkSomeExpression $ MkTuple a' b'
evalE (FstT t) = evalE t >>= \case 
  MkSomeExpression (MkTuple a _) -> pure . MkSomeExpression $ a
  MkSomeExpression (Subtyped @_ @sub t') -> case sing @sub of 
    STCon n (SCons sa (SCons sb SNil)) -> withKnownSymbol n $ case sameSymbol n (SSymbol @"Tuple") of 
      Just Refl ->  withSingI sa $ withSingI sb $ evalE (FstT t')
      _ -> error "Error on evaling 'FstT'-expression. Can only eval tuple arguments"
    _ -> error "Error on evaling 'FstT'-expression. Can only eval tuple arguments"
  _ -> error "Error on evaling 'FstT'-expression. Tuple args normal form can only be tuples or subtyped tuples"
evalE (SndT t) = evalE t >>= \case 
  MkSomeExpression (MkTuple _ b) -> pure . MkSomeExpression $ b
  MkSomeExpression (Subtyped @_ @sub t') -> case sing @sub of 
    STCon n (SCons sa (SCons sb SNil)) -> withKnownSymbol n $ case sameSymbol n (SSymbol @"Tuple") of 
      Just Refl ->  withSingI sa $ withSingI sb $ evalE (SndT t')
      _ -> error "Error on evaling 'FstT'-expression. Can only eval tuple arguments"
    _ -> error "Error on evaling 'FstT'-expression. Can only eval tuple arguments"
  _ -> error "Error on evaling 'FstT'-expression. Tuple args normal form can only be tuples or subtyped tuples"


--------------------------
-- Aux Functions
--------------------------

connector :: Int -> Bool
connector = (> 0)

rConnector :: Bool -> Int
rConnector = \case
  True -> 1
  False -> 0

cTrue :: E m PZ
cTrue = Val  (rConnector True)

cFalse :: E m PZ
cFalse = Val (rConnector False)

infixl 1 $$

($$) :: forall ltype b m. 
    ( SingI b
    , SingI ltype 
    ) => E m (ltype --> b) -> E m ltype -> E m b
($$) f x = App f x

newtype UT = UT String 

instance Show UT where 
  show (UT s) = s

--------------------------
-- Show instance
--------------------------

showRuntimeError :: GammaErrors -> String 
showRuntimeError ((TypeMismatch s (ExpectedType e) (ActualType t))) = concat 
  [ "Variable type Mismatch: " <> show s
  , ". Expected type: " <> show e
  , " But got instead: " <> show t
  ]
showRuntimeError ((VariableNotDefined s))  
  = "Variable not defined: " <> show s
showRuntimeError ((VariableAlreadyDeclared s))
  = "Trying to declare an already existing variable: " <> show s
showRuntimeError ((VariableNotInitialized s))
  = "Trying to use a variable that hasnt been initialized: " <> show s


instance Show (E m a) where
  showsPrec p = \case
    Val  n -> showString (show n)
    Var  x -> showsPrec p . UT . varNameM $ x
    If  c t f -> showParen (p > 10) $ showString "if( " . shows c . showString ", " . shows t . showString ", " . shows f . showString ")"
    Lambda @ltype x t ->  showParen (p > 9) 
      $ showString "fn(" 
      . shows (demote @ltype)
      . showString " "
      . shows (UT $ varNameM  x) 
      . showString " -> " .  showsPrec 0 t
      . showString ")"
    LambdaC @ltype _ x t -> showParen (p > 9)
      $  showString "fn( " 
      . shows (demote @ltype)
      . showString " "
      . shows (UT $ varNameM  x) 
      . showString " -> " .  showsPrec 0 t
      . showString ")"
    App  f a -> showParen (p > 10) $ showsPrec 10 f . showChar '(' . shows a . showChar ')' 
    Defer  v -> showString "'" . showsPrec 11 v . showString "'"
    LazyC _ e -> showsPrec p e -- showChar '<' . showsPrec 10 e . showString  ", " . showsPrec 10 env . showChar '>'
    Formula  e -> showString "formula(" . (shows . UT . varNameM) e . showChar ')'
    Subtyped  e ->  showsPrec p e --showString "@@" . showsPrec p e
    Minus  a b -> showParen (p > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
    Less  a b -> showParen (p > 10) $ showsPrec 4 a . showString " < " . showsPrec 5 b
    Random a  -> showString "random(" . shows a . showChar ')'
    Bottom _ _-> showString "BOTTOM"
    MkTuple a b -> showString "(" . shows a . showString ", " . shows b . showString ")"
    FstT a -> showString "fst(" . shows a . showString ")"
    SndT a -> showString "snd(" . shows a . showString ")"



 
---------------------------
-- Standard library
---------------------------

fstStd :: forall x a b m. (Ftype x ~ PTuple a b, SingI x, SingI a, SingI b, Effects m) => E m (x --> a)
fstStd 
  = withSingIFtype @a 
  $ withSingIFtype @b 
  $ Lambda "t"
  $ FstT (Var @x "t")


sndStd :: forall x a b m. (Ftype x ~ PTuple a b, SingI x, SingI a, SingI b, Effects m) => E m (x --> b)
sndStd 
  = withSingIFtype @a 
  $ withSingIFtype @b 
  $ Lambda "t"
  $ SndT (Var @x "t")


randomStd :: Effects m => E m (PZ --> PZ)
randomStd 
  = Lambda "x"
  $ Random (Var @(PZ) "x")

minusStd :: Effects m => E m (PZ --> PZ --> PZ)
minusStd 
  = Lambda "l"
  $ Lambda "r"
  $ Minus (Var @(PZ) "l") (Var @(PZ) "r")
 

plusStd :: Effects m => E m (PZ --> PZ --> PZ)
plusStd 
  = Lambda "l"
  $ Lambda "r"
  $ Minus (Var @(PZ) "l") 
    (Minus (Val 0) (Var @(PZ) "r"))
  

ltStd :: Effects m => E m (PZ --> PZ --> PZ)
ltStd 
  = Lambda "l"
  $ Lambda "r"
  $ Less (Var @(PZ) "l") (Var @(PZ) "r")

eqStd ::Effects m => E m (PZ --> PZ --> PZ)
eqStd
  = Lambda "l"
  $ Lambda "r"
  $ (Var @(PZ --> PZ --> PZ) "and")
    $$  ( (Var @(PZ --> PZ) "not") 
        $$  Less (Var @(PZ) "l") (Var @(PZ) "r")
        )
    $$  ( (Var @(PZ --> PZ) "not") 
        $$  Less (Var @(PZ) "r") (Var @(PZ) "l")
        )

gtStd :: Effects m => E m (PZ --> PZ --> PZ)
gtStd
  = Lambda "l"
  $ Lambda "r"
  $ (Var @(PZ --> PZ --> PZ) "and") 
  $$ (Less (Var @(PZ) "r") (Var @(PZ) "l"))
  $$  (  Var @(PZ --> PZ) "not"
      $$  ( Var @(PZ --> PZ --> PZ) "eq"
          $$ (Var @(PZ) "l")
          $$ (Var @(PZ) "r")
          )
      )



orStd :: Effects m => E m (PZ --> PZ --> PZ)
orStd
  = Lambda "l"
  $ Lambda "r"
  $ If 
    (Var @(PZ) "l")
    (cTrue)
    $ If 
      (Var @(PZ) "r")
      (cTrue)
      (cFalse)


notStd :: Effects m => E m (PZ --> PZ)
notStd
  = Lambda "l"
  $ If 
    (Var @(PZ) "l")
    (cFalse)
    (cTrue)
  

andStd :: Effects m => E m (PZ --> PZ --> PZ)
andStd
  = Lambda "l"
  $ Lambda "r"
  $ If 
    (Var @(PZ) "l")
    ( If 
      (Var @(PZ) "r")
      (cTrue)
      (cFalse)
    )
    (cFalse)
  



ltEqStd :: Effects m => E m (PZ --> PZ --> PZ)
ltEqStd 
  = Lambda "l"
  $ Lambda "r"
  $   ( Var @(PZ --> PZ --> PZ) "or")
  $$  ( Less (Var @(PZ) "l") (Var @(PZ) "r") )
  $$  ( Var @(PZ --> PZ --> PZ) "eq" 
      $$ (Var @(PZ) "l")
      $$ (Var @(PZ) "r")
      )
  

gtEqStd :: Effects m => E m (PZ --> PZ --> PZ)
gtEqStd 
  = Lambda "l"
  $ Lambda "r"
  $   ( Var @(PZ --> PZ --> PZ) "or")
  $$  ( (Var @(PZ --> PZ --> PZ) "gt")
      $$ (Var @(PZ) "l") 
      $$ (Var @(PZ) "r") )
  $$  ( Var @(PZ --> PZ --> PZ) "eq" 
      $$ (Var @(PZ) "l")
      $$ (Var @(PZ) "r")
      )
  

nEqStd :: Effects m => E m (PZ --> PZ --> PZ)
nEqStd 
  = Lambda "l"
  $ Lambda "r"
  $ (Var @(PZ --> PZ) "not")
  $$  ( Var @(PZ --> PZ --> PZ) "eq" 
      $$ (Var @(PZ) "l")
      $$ (Var @(PZ) "r")
      )
  
absStd :: Effects m => E m (PZ --> PZ)
absStd 
  = Lambda "x"
  $ If 
    (Less (Var @(PZ) "x") (Val 0)) 
    (Minus (Val 0) (Var @(PZ) "x"))
    (Var @(PZ) "x")

chsStd :: Effects m => E m (PZ --> PZ)
chsStd 
  = Lambda "x"
  $ Minus (Val 0) (Var @(PZ) "x")


_mltStd :: Effects m => E m (PZ --> PZ --> PZ)
_mltStd 
  = Lambda "l"
  $ Lambda "r"
  $ If 
    (  Var @(PZ --> PZ --> PZ) "eq" 
    $$ Var @(PZ) "l"
    $$ Val 0
    )
    (Val 0)
    ( Var @(PZ --> PZ --> PZ) "plus"
    $$  ( Var @(PZ --> PZ --> PZ) "_mlt"
        $$ (Minus (Var @(PZ) "l") (Val 1))
        $$ (Var @(PZ) "r")
        )
    $$ (Var @(PZ) "r")
    )

_mulStd :: Effects m => E m (PZ --> PZ --> PZ)
_mulStd 
  = Lambda "l"
  $ Lambda "r"
  $ If 
    (Less 
      (Val 0)
      (Var @(PZ) "l")
    )
    ( Var @(PZ --> PZ --> PZ) "_mlt" 
    $$ Var @(PZ) "l"
    $$ Var @(PZ) "r"
    )
    ( (Var @(PZ --> PZ) "chs")
    $$  ( Var @(PZ --> PZ --> PZ) "_mlt" 
        $$ Var @(PZ) "l"
        $$ Var @(PZ) "r"
        )
    )

mulStd :: Effects m => E m (PZ --> PZ --> PZ)
mulStd 
  = Lambda "l"
  $ Lambda "r"
  $ If 
    (Less 
      (Var @(PZ --> PZ) "abs" $$ Var @(PZ) "l") 
      (Var @(PZ --> PZ) "abs" $$ Var @(PZ) "r") 
    )
    (  (Var @(PZ --> PZ --> PZ) "_mul" )
    $$ (Var @(PZ) "l")
    $$ (Var @(PZ) "r")
    )
    (  (Var @(PZ --> PZ --> PZ) "_mul" )
    $$ (Var @(PZ) "r")
    $$ (Var @(PZ) "l")
    ) 



