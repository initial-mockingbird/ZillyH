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
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE OverloadedStrings          #-}
--{-# LANGUAGE TypeAbstractions #-}

{-|
Module      : Zilly.Classic.Expression
Description : Defines the contexts of expressions and its rvalue rules for classic zilly.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Zilly.Classic.Expression where

import Utilities.LensM
import Utilities.TypedMap
import Zilly.Types
import Zilly.ADT.Expression
import Zilly.RValue
import Zilly.Upcast
import Zilly.Classic.Interpreter

import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Control.Monad.Reader 
import Control.Monad

import Control.Applicative
import Prelude.Singletons (SingI,SMaybe(..),sing,withSingI)

import Data.Singletons.Decide
import Data.Function.Singletons
import Debug.Trace (trace)
import Data.Functor.Identity (Identity(..))
import Utilities.ShowM



--------------------------
-- Aux Functions
--------------------------

-- | Bottom value. Useful for pattern synonyms.
bottom :: Void
bottom = error "Attempt to evaluate void"

-- | Absurd proof. Useful for pattern synonyms.
absurd :: Void -> a
absurd m = case m of {}


connector :: Int -> Bool
connector = (> 0)

rConnector :: Bool -> Int
rConnector = \case
  True -> 1
  False -> 0

cTrue ::  forall. E ExprTag (Value Z)
cTrue = ValE  (rConnector True)

cFalse :: E ExprTag (Value Z)
cFalse = ValE (rConnector False)

cvalue :: forall {env} a  (m :: Type -> Type). 
  (Gamma m ~ env, MonadReader env m) => LensM m a -> m a
cvalue l = ask >>= viewM l
  

--------------------------
-- Tag
--------------------------

data ExprTag

type instance AssocCtxMonad ExprTag = TaggedInterpreter ExprTag
type instance Gamma (TaggedInterpreter ExprTag) = TypeRepMap ExprTag

--------------------------
-- Expression language
--------------------------

type instance ValX ExprTag = Void
pattern ValE ::  Int -> E ExprTag (Value Z) 
pattern ValE n <- Val _ n
  where ValE n = Val bottom n



type instance ValueCX ExprTag a = Void
pattern ValueCE :: (E ExprTag (Value a), Gamma (AssocCtxMonad ExprTag)) -> E ExprTag (Value a)
pattern ValueCE n <- ValueC _ n
  where ValueCE n = ValueC bottom n


type instance ClosureX ExprTag a = Void
pattern ClosureE :: (E ExprTag a,Gamma (AssocCtxMonad ExprTag)) -> E ExprTag a 
pattern ClosureE n <- Closure _ n
  where ClosureE n = Closure bottom n


type instance VarX ExprTag env = Void
pattern VarE :: LensM (AssocCtxMonad ExprTag) (E ExprTag a) -> E ExprTag a
pattern VarE n <- Var _ n
  where VarE n = Var bottom n


type instance DeferX ExprTag a =
  ( Proof (RValue ExprTag) a
  , Proof SingI a
  , Proof SingI (RValueT a)
  )
pattern DeferE :: 
  ( RValue ExprTag a
  , SingI a
  , SingI (RValueT a)
  ) 
  => E ExprTag a -> E ExprTag (Lazy a) 
pattern DeferE n <- Defer _ n
  where DeferE n = Defer (P,P,P) n


type instance FormulaX ExprTag a = Void
pattern FormulaE :: LensM (AssocCtxMonad ExprTag) (E ExprTag a) -> E ExprTag (Lazy a)
pattern FormulaE n <- Formula _ n
  where FormulaE n = Formula bottom n


type instance ExpX ExprTag a = Void
pattern ExpE :: Void -> E ExprTag a
pattern ExpE v <- Exp v
  where ExpE v = absurd v


type instance LambdaCX ExprTag a b = Proof (RValue ExprTag) b
pattern LambdaCE :: 
  ( RValue ExprTag b
  )
  => (Gamma (AssocCtxMonad ExprTag), LensM (AssocCtxMonad ExprTag) (E ExprTag a), E ExprTag b) 
  -> E ExprTag (a ~> b)
pattern LambdaCE n <- LambdaC _ n
  where LambdaCE n = LambdaC P n


type instance SubtypedX ExprTag a b =
  ( Proof ((~) (UpperBound (RValueT a) b)) (Just b)
  , Proof SingI a
  , Proof SingI b
  , Proof (RValue ExprTag) a
  , Proof (RValue ExprTag) b
  )
pattern SubtypedE :: forall b. (SingI b, RValue ExprTag b) => forall a. 
  ( UpperBound (RValueT a) b ~ Just b
  , SingI a
  , RValue ExprTag a
  ) => E ExprTag a -> E ExprTag b
--pattern SubtypedE n = Subtyped (P,P,P,P,P) n
pattern SubtypedE n <- Subtyped (P,P,P,P,P) n
  where SubtypedE n = Subtyped (P,P,P,P,P) n




type instance MinusX ExprTag a b = 
  ( Proof (RValue ExprTag) a
  , Proof (RValue ExprTag) b
  , Proof ((~) (RValueT a)) (Value Z)
  , Proof ((~) (RValueT b)) (Value Z)
  )

pattern MinusE :: () =>
  ( RValue ExprTag a
  , RValue ExprTag b
  , RValueT a ~ Value Z
  , RValueT  b ~ Value Z
  ) 
  => E ExprTag a -> E ExprTag b -> E ExprTag (Value Z)
pattern MinusE a b <- Minus (P,P,P,P) a b
  where MinusE a b = Minus (P,P,P,P) a b

type instance LessX ExprTag a b =
  ( Proof (RValue ExprTag) a
  , Proof (RValue ExprTag) b
  , Proof ((~) (RValueT a)) (Value Z)
  , Proof ((~) (RValueT b)) (Value Z)
  )
pattern LessE :: () =>
  ( RValue ExprTag a
  , RValue ExprTag b
  , RValueT a ~ Value Z
  , RValueT  b ~ Value Z
  ) 
  => E ExprTag a -> E ExprTag b -> E ExprTag (Value Z)
pattern LessE a b <- Less (P,P,P,P) a b
  where LessE a b = Less (P,P,P,P) a b

type instance LambdaX ExprTag a b =
  ( Proof (RValue ExprTag) b
  , Proof SingI a
  , Proof SingI b
  )
pattern LambdaE :: 
  ( RValue ExprTag b
  , SingI a
  , SingI b
  )
  => LensM (AssocCtxMonad ExprTag) (E ExprTag a) -> E ExprTag b  -> E ExprTag (a ~> b)
pattern LambdaE n m <- Lambda _ n m
  where LambdaE n m = Lambda (P,P,P) n m


type instance AppX ExprTag f x arg b = 
  ( Proof (RValue ExprTag) f
  , Proof (RValue ExprTag) x
  , Proof ((~) (RValueT f)) (arg ~> b)
  , Proof ((~) (UpperBound (RValueT x) arg)) (Just arg)
  , Proof SingI f
  , Proof SingI x
  , Proof SingI arg
  , Proof SingI b
  )
pattern AppE :: forall b. (SingI b) => forall f x arg . 
    ( RValue ExprTag f
    , RValue ExprTag x
    , RValueT f ~ (arg ~> b)
    , UpperBound (RValueT x) arg ~ Just arg
    , SingI f
    , SingI x
    , SingI arg
    ) => E ExprTag f -> E ExprTag x -> E ExprTag b
pattern AppE f x = App (P,P,P,P,P,P,P,P) f x
--pattern AppE f x <- App _ f x
--  where AppE f x = App (P,P,P,P,P,P,P,P) f x 

infixl 1 $$

($$) :: forall b . (SingI b) => forall x arg1. 
    ( RValue ExprTag arg1 
    , RValue ExprTag x
    , UpperBound (RValueT x) arg1 ~ Just arg1
    , SingI arg1
    , SingI x
    ) => E ExprTag (arg1 ~> b) -> E ExprTag x -> E ExprTag b
($$) f x = AppE f x



type instance IfX ExprTag x0 x1 x2 x3 = 
  ( Proof (RValue ExprTag) x0
  , Proof (RValue ExprTag) x1
  , Proof (RValue ExprTag) x2
  , Proof ((~) (RValueT x0)) (Value Z)
  , Proof ((~) (UpperBound (RValueT x1) (RValueT x2))) (Just x3)
  , Proof SingI x1
  , Proof SingI x2
  , Proof SingI x3
  )
pattern IfE :: forall x3. (SingI x3) => forall x0 x1 x2. 
  ( RValue ExprTag x0
  , RValue ExprTag x1
  , RValue ExprTag x2
  , RValueT x0 ~ Value Z
  , UpperBound (RValueT x1) (RValueT x2) ~ Just x3
  , SingI x1
  , SingI x2
  ) => E ExprTag x0 -> E ExprTag x1 -> E ExprTag x2 -> E ExprTag x3
pattern IfE x0 x1 x2 <- If (P,P,P,P,P,P,P,P) x0 x1 x2
  where IfE x0 x1 x2 = If (P,P,P,P,P,P,P,P) x0 x1 x2


instance 
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  , MonadFail (AssocCtxMonad ExprTag)
  ) => RValue ExprTag (Value a) where

  rvalue (Val _ n)             = pure (ValE n)
  rvalue (ValueC _ (e,gamma))  = localM (pure . const gamma) $ rvalue e
  rvalue (Minus (P,P,P,P) a b) = (,) <$> rvalue a <*> rvalue b >>= \case
    (ValE a', ValE b') -> pure $ ValE (a' - b')
    (a',b') ->  liftA2 MinusE  (rvalue a') (rvalue b') >>= rvalue
  rvalue (Less (P,P,P,P) a b)  = (,) <$> rvalue a <*> rvalue b >>= \case
    (ValE a', ValE b') -> pure $ ValE (rConnector $ a' < b')
    (a',b') -> liftA2 LessE  (rvalue a') (rvalue b') >>= rvalue
  rvalue (LambdaC P gamma)     = pure $ LambdaCE gamma
  rvalue (Lambda (P,P,P) x t)  = do
    gamma <- ask
    pure $ LambdaCE (gamma,x,t)
  rvalue e@(App {})      = genRVApp e
  rvalue v@(Var {})      = genRVVar v
  rvalue e@(Closure {})  = genRVClosure e
  rvalue e@(Subtyped {}) = genRVSubtyped e
  rvalue e@(If (P,P,P,P,P,P,P,P) _ _ _)  = genRVIf e
  rvalue (Exp v) = absurd v 
  

instance  
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  , MonadFail (AssocCtxMonad ExprTag)

  ) => RValue ExprTag (Lazy a) where
    rvalue (Defer (P,P,P) v) = genRVDefer (DeferE v)
    rvalue e@(App {})        = genRVApp e
    rvalue e@(Closure {})    = genRVClosure e
    rvalue v@(Var {})        = genRVVar v
    rvalue (Formula _ e)     = cvalue e
    rvalue e@(Subtyped {})   = genRVSubtyped e
    rvalue e@(If (P,P,P,P,P,P,P,P) _ _ _)  = genRVIf e
    rvalue (Exp v)           = absurd v 

instance RValue ExprTag (Array x) where 
    rvalue = error "TODO"
instance RValue ExprTag (LazyS x) where 
    rvalue = error "TODO"


------------------------------
-- Generic R-Value Functions
------------------------------

genRVar :: 
  ( MonadIO (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  , RValue ExprTag a
  , RValueT a ~ c
  ) => E ExprTag a -> (AssocCtxMonad ExprTag) (E ExprTag c)
genRVar (VarE x) = rvalue <=< cvalue $ x
genRVar _ = undefined

genRVIf ::forall {x4 :: Types} {m :: Type -> Type} (x3 :: Types) .
  ( SingI x3
  , RValue ExprTag x3
  , RValueT x3 ~ x4
  , AssocCtxMonad ExprTag ~ m
  , MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  )
  => E ExprTag x3 -> m (E ExprTag x4)
genRVIf (If @_ @(x0 :: Types) @(x1 :: Types) @(x2 :: Types) (P,P,P,P,P,P,P,P) cond t f) 
  = withSingIRType @x1
  $ withSingIRType @x2
  $ rvalue cond >>= \case
    ValE (connector -> True) -> do 
      t' <- rvalue t
      withSingIRType @x3 $ case upcast @_ @_ @x4  UpcastE t' of
        SameTypeUB t'' -> pure t''
        RightUB t'' -> pure t''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    ValE (connector -> False) -> do 
      f' :: E ExprTag c1 <- rvalue f
      withSingIRType @x3 $ case upcast @_ @_ @x4 UpcastE f' of
        SameTypeUB f'' -> pure f''
        RightUB f'' -> pure f''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    c' -> rvalue (IfE c' t f)
genRVIf _ = undefined

genRVApp ::
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  , RValue ExprTag b
  , MonadFail (AssocCtxMonad ExprTag)

  ) => E ExprTag b -> (AssocCtxMonad ExprTag) (E ExprTag (RValueT b))
genRVApp (App @_ @f @x @b @arg (P,P,P,P,P,P,P,P) f a) = rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> withSingIRType @x  $ do
      arg <- rvalue a >>= \rva -> case upcast @ExprTag @_ @arg UpcastE rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        -- these two can only happen when the types are equal
        -- but I have yet to find a stricter constraint that expresses this.
        LeftUB _          -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      t'  <- localM (setMF x arg . const gamma) $ rvalue t
      gamma' <- setMF x arg gamma
      pure $ ClosureE  (t',gamma')
    (Subtyped @_ (P,P,P,P,P) e1) -> fail "general function subtyping"
    f' ->  rvalue $ AppE f' a
genRVApp _ = undefined

genRVDefer :: 
  ( RValue ExprTag a
  , SingI a
  , SingI (RValueT a)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) m
  ) => E ExprTag (Lazy a) -> m (E ExprTag a)
genRVDefer (DeferE v) = do
  gamma <- ask 
  pure $ ClosureE (v,gamma)
genRVDefer _ = undefined

genRVClosure :: 
  ( MonadReader (Gamma (AssocCtxMonad ctx)) (AssocCtxMonad ctx)
  ,  RValue ctx a
  ) => E ctx a -> AssocCtxMonad ctx (E ctx (RValueT a))
genRVClosure (Closure _ (e,gamma)) = localM (pure . const gamma) $ rvalue e
genRVClosure _  = undefined


genRVVar :: 
  ( RValue ctx a
  ,  MonadReader (Gamma (AssocCtxMonad ctx)) (AssocCtxMonad ctx)
  ) => E ctx a -> AssocCtxMonad ctx (E ctx (RValueT a))
genRVVar (Var _ x) = rvalue <=< cvalue $ x
genRVVar _ = undefined

genRVSubtyped ::
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  ) => E ExprTag b -> (AssocCtxMonad ExprTag) (E ExprTag (RValueT b))
genRVSubtyped (Subtyped @_ @e1 @e2 (P,P,P,P,P) e1) = do
    --trace "rvaluing a subtyped" pure ()
    e1' :: E ExprTag (RValueT  e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E ExprTag (RValueT e2) 
          = withRVType @ExprTag (sing @e1) 
          $ withSingIRType @e1
          $ withSingIRType @e2
          $ withRVType @ExprTag (sing @(RValueT e1)) 
          $ withRVType @ExprTag (sing @(RValueT e2)) 
          $ rvaluePreservesST @(RValueT e1) @e2 
          $ SubtypedE e1'
    pure e1''
genRVSubtyped _ = undefined

------------------------------
-- How ExprTag upcasts.
------------------------------

type instance UpcastX ExprTag a b = 
  ( Dict (SingI a)
  , Dict (SingI b)
  , Dict (CS (RValue ExprTag) ValueSym0 ) 
  , Dict (CS (RValue ExprTag) (LazySym0 .@#@$$$ LazySym0))
  , Dict (CS (RValue ExprTag) (LazySym0 .@#@$$$ ValueSym0))
  )
pattern UpcastE :: forall a b.
  ( SingI a 
  , SingI b
  , forall t. RValue ExprTag (Value t)
  , forall t. RValue ExprTag (Lazy (Lazy t))
  , forall t. RValue ExprTag (Lazy (Value t))
  ) => UpcastX ExprTag a b
pattern UpcastE  <-(Dict,Dict,Dict,Dict,Dict)
  where UpcastE  = (Dict,Dict,Dict,Dict,Dict)


-- instance Upcast ExprTag where
--   upcast :: forall a b. UpcastX ExprTag a b -> E ExprTag a -> UpperBoundResults (E ExprTag) a b
--   upcast (Dict,Dict,Dict,Dict,Dict) f 
--     = withSingIUBType @a @b 
--     $ case decideEquality (sing @a) (sing @b) of
--       Just Refl -> ubIsIdempotent @a $ SameTypeUB f
--       Nothing -> case sing @(UpperBound a b) of
--         SJust @_ @n sub -> case decideEquality (sing @a) sub of
--           Just Refl -> LeftUB f
--           Nothing   -> case decideEquality (sing @b) sub of
--             Just Refl 
--               -> rvalueIsPred @a
--               $ withSingIRType @a
--               $ ubIsTransitive' @(RValueT a) @a @b 
--               $ withRVType @ExprTag (sing @a) 
--               $ withRVType @ExprTag (sing @b) 
--               $ RightUB (SubtypedE f)
--             Nothing   
--               -> withRVType @ExprTag (sing @a) 
--               $ withSingI sub
--               $ withRVType @ExprTag (sing @n) 
--               $ subtyped'CTX @ExprTag @a @b 
--               $ SomethingElseUB (SubtypedE f)
--         SNothing  -> NonExistentUB
--


instance Upcast ExprTag where
  upcast :: forall a b. UpcastX ExprTag a b -> E ExprTag a -> UpperBoundResults (E ExprTag) a b
  upcast (Dict,Dict,Dict,Dict,Dict) f 
    = withSingIUBType @a @b 
    $ case decideEquality (sing @a) (sing @b) of
      Just Refl -> ubIsIdempotent @a $ SameTypeUB f
      Nothing -> case sing @(UpperBound a b) of
        SJust @_ @n sub -> case decideEquality (sing @a) sub of
          Just Refl -> LeftUB f
          Nothing   -> case decideEquality (sing @b) sub of
            Just Refl 
              -> rvalueIsPred @a
              $ withSingIRType @a
              $ ubIsTransitive' @(RValueT a) @a @b 
              $ withRVType @ExprTag (sing @a) 
              $ withRVType @ExprTag (sing @b) 
              $ RightUB (SubtypedE f)
            Nothing   
              -> withRVType @ExprTag (sing @a) 
              $ withSingI sub
              $ withRVType @ExprTag (sing @n) 
              $ subtyped'CTX @ExprTag @a @b 
              $ SomethingElseUB (SubtypedE f)
        SNothing  -> NonExistentUB

class SatUpcast (a :: Types) (b :: Types) where 
  satUpcast :: UpcastX ExprTag a b -> E ExprTag a -> UpperBoundResults (E ExprTag) a b

instance SatUpcast (Value Z) (Value Z) where 
  satUpcast _ a = SameTypeUB a


---------------------------
-- Show instances
---------------------------

instance Monad m => ShowM m (E ExprTag a) where
  showsPrecM p = \case
    Val _ n -> showsPrecM p n
    ValueC _ (e,_) -> showsPrecM p e
    Var _ x -> showsPrecM p . UT . varNameM $ x
    Minus _ a b -> showParenM (p > 6) $ showsPrecM 6 a <=< showStringM " - " <=< showsPrecM 7 b
    Less _ a b -> showParenM (p > 10) $ showsPrecM 4 a <=< showStringM " < " <=< showsPrecM 5 b
    If _ c t f -> showParenM (p > 10) $ showStringM "if (" <=< showsM c <=< showStringM ", " <=< showsM t <=< showStringM ", " <=< showsM f <=< showCharM ')'
    Lambda _ x t -> showParenM (p > 9) $ showStringM "fn " <=< showsPrecM 10 (UT . varNameM $ x) <=< showStringM " -> " <=<  showsPrecM 0 t
    LambdaC _ (_,x,t) -> showParenM (p > 9) $  showStringM "fn " <=< showsPrecM 10 (UT . varNameM $ x) <=< showStringM " -> " <=< showsPrecM 10 t
 
    App _ f a -> showParenM (p > 10) $ showsPrecM 10 f <=< showCharM '(' <=< showsM a <=< showCharM ')'
    Defer _ v -> showStringM "'" <=< showsPrecM 11 v <=< showStringM "'"
    Closure _ (e,_) -> showsPrecM p e 
    Formula _ e -> showStringM "formula(" <=< (showsM . UT . varNameM) e <=< showCharM ')'
    -- FEval  _ -> undefined
    -- DeferS _ -> undefined
    Subtyped _ e -> showsPrecM p e
    Exp _ -> showStringM "no additional extensions"

---------------------------
-- Standard library
---------------------------


minusStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
minusStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ MinusE (VarE @(Value Z) "l") (VarE @(Value Z) "r")
  

plusStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
plusStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ MinusE (VarE @(Value Z) "l") 
    (MinusE (ValE 0) (VarE @(Value Z) "r"))
  

ltStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
ltStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ LessE (VarE @(Value Z) "l") (VarE @(Value Z) "r")
  
-- check 42 = 42
-- check 42 <> 42 parsing error
eqStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
eqStd
  = LambdaE "l"
  $ LambdaE "r"
  $ (VarE @(Value Z ~> Value Z ~> Value Z) "and")
    $$  ( (VarE @(Value Z ~> Value Z) "not") 
        $$  LessE (VarE @(Value Z) "l") (VarE @(Value Z) "r")
        )
    $$  ( (VarE @(Value Z ~> Value Z) "not") 
        $$  LessE (VarE @(Value Z) "r") (VarE @(Value Z) "l")
        )

gtStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
gtStd
  = LambdaE "l"
  $ LambdaE "r"
  $ (VarE @(Value Z ~> Value Z ~> Value Z) "and") 
  $$ (LessE (VarE @(Value Z) "r") (VarE @(Value Z) "l"))
  $$  (  VarE @(Value Z ~> Value Z) "not"
      $$  ( VarE @(Value Z ~> Value Z ~> Value Z) "eq"
          $$ (VarE @(Value Z) "l")
          $$ (VarE @(Value Z) "r")
          )
      )



orStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
orStd
  = LambdaE "l"
  $ LambdaE "r"
  $ IfE 
    (VarE @(Value Z) "l")
    (cTrue)
    $ IfE 
      (VarE @(Value Z) "r")
      (cTrue)
      (cFalse)


notStd :: E ExprTag (Value Z ~> Value Z)
notStd
  = LambdaE "l"
  $ IfE 
    (VarE @(Value Z) "l")
    (cFalse)
    (cTrue)
  

andStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
andStd
  = LambdaE "l"
  $ LambdaE "r"
  $ IfE 
    (VarE @(Value Z) "l")
    ( IfE 
      (VarE @(Value Z) "r")
      (cTrue)
      (cFalse)
    )
    (cFalse)
  



ltEqStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
ltEqStd 
  = LambdaE "l"
  $ LambdaE "r"
  $   ( VarE @(Value Z ~> Value Z ~> Value Z) "or")
  $$  ( LessE (VarE @(Value Z) "l") (VarE @(Value Z) "r") )
  $$  ( VarE @(Value Z ~> Value Z ~> Value Z) "eq" 
      $$ (VarE @(Value Z) "l")
      $$ (VarE @(Value Z) "r")
      )
  

gtEqStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
gtEqStd 
  = LambdaE "l"
  $ LambdaE "r"
  $   ( VarE @(Value Z ~> Value Z ~> Value Z) "or")
  $$  ( (VarE @(Value Z ~> Value Z ~> Value Z) "gt")
      $$ (VarE @(Value Z) "l") 
      $$ (VarE @(Value Z) "r") )
  $$  ( VarE @(Value Z ~> Value Z ~> Value Z) "eq" 
      $$ (VarE @(Value Z) "l")
      $$ (VarE @(Value Z) "r")
      )
  

nEqStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
nEqStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ (VarE @(Value Z ~> Value Z) "not")
  $$  ( VarE @(Value Z ~> Value Z ~> Value Z) "eq" 
      $$ (VarE @(Value Z) "l")
      $$ (VarE @(Value Z) "r")
      )
  
absStd :: E ExprTag (Value Z ~> Value Z)
absStd 
  = LambdaE "x"
  $ IfE 
    (LessE (VarE @(Value Z) "x") (ValE 0)) 
    (MinusE (ValE 0) (VarE @(Value Z) "x"))
    (VarE @(Value Z) "x")

chsStd :: E ExprTag (Value Z ~> Value Z)
chsStd 
  = LambdaE "x"
  $ MinusE (ValE 0) (VarE @(Value Z) "x")


_mltStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
_mltStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ IfE 
    (  VarE @(Value Z ~> Value Z ~> Value Z) "eq" 
    $$ VarE @(Value Z) "l"
    $$ ValE 0
    )
    (ValE 0)
    ( VarE @(Value Z ~> Value Z ~> Value Z) "plus"
    $$  ( VarE @(Value Z ~> Value Z ~> Value Z) "_mlt"
        $$ (MinusE (VarE @(Value Z) "l") (ValE 1))
        $$ (VarE @(Value Z) "r")
        )
    $$ (VarE @(Value Z) "r")
    )

_mulStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
_mulStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ IfE 
    (LessE 
      (ValE 0)
      (VarE @(Value Z) "l")
    )
    ( VarE @(Value Z ~> Value Z ~> Value Z) "_mlt" 
    $$ VarE @(Value Z) "l"
    $$ VarE @(Value Z) "r"
    )
    ( (VarE @(Value Z ~> Value Z) "chs")
    $$  ( VarE @(Value Z ~> Value Z ~> Value Z) "_mlt" 
        $$ VarE @(Value Z) "l"
        $$ VarE @(Value Z) "r"
        )
    )

mulStd :: E ExprTag (Value Z ~> Value Z ~> Value Z)
mulStd 
  = LambdaE "l"
  $ LambdaE "r"
  $ IfE 
    (LessE 
      (VarE @(Value Z ~> Value Z) "abs" $$ VarE @(Value Z) "l") 
      (VarE @(Value Z ~> Value Z) "abs" $$ VarE @(Value Z) "r") 
    )
    (  (VarE @(Value Z ~> Value Z ~> Value Z) "_mul" )
    $$ (VarE @(Value Z) "l")
    $$ (VarE @(Value Z) "r")
    )
    (  (VarE @(Value Z ~> Value Z ~> Value Z) "_mul" )
    $$ (VarE @(Value Z) "r")
    $$ (VarE @(Value Z) "l")
    ) 



