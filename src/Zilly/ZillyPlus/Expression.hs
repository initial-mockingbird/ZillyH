{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
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
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE TypeAbstractions           #-}

{-|
Module      : Zilly.Classic.Expression
Description : Defines the contexts of expressions and its rvalue rules for classic zilly.
Copyright   : (c) Daniel Dictinto, 2024
                  Enzo Alda, 2024
License     : GDictL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Dictortability : DictOSIX

-}
module Zilly.ZillyPlus.Expression where

import Data.Proof
import Utilities.LensM
import Utilities.TypedMapPlus
import Zilly.Types
import Zilly.ADT.ExpressionPlus
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter

import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Control.Monad.Reader 
import Control.Monad

import Control.Applicative
import Prelude.Singletons (SingI,SMaybe(..),sing,withSingI)

import Data.Singletons.Decide
import Utilities.ShowM
import Prelude hiding (LT,GT,EQ)
import Data.Maybe.Singletons (IsJust,FromJust)

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

rConnector :: Num a => Bool -> a
rConnector = \case
  True ->  1
  False -> -1

cTrue :: E Void2 sub ExprTag (Value Z)
cTrue = ValE  (rConnector True)

cFalse :: E Void2 sub ExprTag (Value Z)
cFalse = ValE (rConnector False)

cvalue :: forall {env} a  (m :: Type -> Type). 
  (Gamma m ~ env, MonadReader env m) => LensM m a -> m a
cvalue l = ask >>= viewM l
  

--------------------------
-- Tag
--------------------------



type family BasicValue (a :: Types) :: Maybe Type where
  BasicValue (Value Z) = Just Int
  BasicValue (Value F) = Just Double
  BasicValue _         = Nothing


data ExprTag

type instance AssocCtxMonad ExprTag = TaggedInterpreter ExprTag

--------------------------
-- Expression language
--------------------------

type instance ValX sub ExprTag a = 
  ( Dict (IsJust (BasicValue a) ~ True) 
  , FromJust (BasicValue a)
  , Dict (Show (FromJust (BasicValue a)))
  )
pattern ValE :: forall a b sub. 
  ( BasicValue a ~ Just b
  , Show (FromJust (BasicValue a))
  ) =>  b -> E Void2 sub ExprTag a
pattern ValE n <- Val (Dict,n,Dict)
  where ValE n = Val (Dict,n,Dict)



type instance ValueCX sub ExprTag a = 
  ( Dict (IsJust (BasicValue a) ~ True) 
  , E Void2 sub ExprTag a
  )

pattern ValueCE :: forall {b} a sub. (BasicValue a ~ Just b) 
  => E Void2 sub ExprTag a -> Gamma (AssocCtxMonad ExprTag) -> E Void2 sub ExprTag a
pattern ValueCE a b <- ValueC (Dict,a) b
  where ValueCE a b = ValueC (Dict,a) b


type instance ClosureX sub ExprTag a = Void
pattern ClosureE :: (E Void2 sub ExprTag a,Gamma (AssocCtxMonad ExprTag)) -> E Void2 sub ExprTag a 
pattern ClosureE n <- Closure _ n
  where ClosureE n = Closure bottom n


type instance VarX sub ExprTag env = Void
pattern VarE :: LensM (AssocCtxMonad ExprTag) (E Void2 sub ExprTag a) -> E Void2 sub ExprTag a
pattern VarE n <- Var _ n
  where VarE n = Var bottom n


type instance DeferX sub ExprTag a =
  ( Dict (RValue (E Void2 sub ExprTag)  a)
  , Dict (SingI a)
  , Dict (SingI (RValueT a))
  )
pattern DeferE :: 
  ( RValue (E Void2 sub ExprTag) a
  , SingI a
  , SingI (RValueT a)
  ) 
  => E Void2 sub ExprTag a -> E Void2 sub ExprTag (Lazy a) 
pattern DeferE n <- Defer _ n
  where DeferE n = Defer (Dict,Dict,Dict) n


type instance FormulaX sub ExprTag a = Void
pattern FormulaE :: LensM (AssocCtxMonad ExprTag) (E Void2 sub ExprTag a) -> E Void2 sub ExprTag (Lazy a)
pattern FormulaE n <- Formula _ n
  where FormulaE n = Formula bottom n

type instance LambdaCX sub ExprTag a b = Dict ((RValue (E Void2 sub ExprTag) ) b)
pattern LambdaCE :: forall a b sub.  
  ( RValue (E Void2 sub ExprTag) b
  )
  => (Gamma (AssocCtxMonad ExprTag), Maybe (LensM (AssocCtxMonad ExprTag) (E Void2 sub ExprTag a)), E Void2 sub ExprTag b) 
  -> E Void2 sub ExprTag (a ~> b)
pattern LambdaCE n <- LambdaC _ n
  where LambdaCE n = LambdaC Dict n


type instance SubtypedX sub ExprTag a b =
  ( Dict (((~) (UpperBound (RValueT a) b)) (Just b))
  , Dict (SingI a)
  , Dict (SingI b)
  , Dict ((RValue (E Void2 sub ExprTag) ) a)
  , Dict ((RValue (E Void2 sub ExprTag) ) b)
  , Dict (TypesCaseAnalysis (RValue (E Void2 sub ExprTag)))
  , Dict (AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub))
  )
pattern SubtypedE :: forall sub b. 
  ( SingI b
  , RValue (E Void2 sub ExprTag) b
  , TypesCaseAnalysis (RValue (E Void2 sub ExprTag))
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)
  ) => forall a. 
    ( UpperBound (RValueT a) b ~ Just b
    , SingI a
    , RValue (E Void2 sub ExprTag)  a
    ) => E Void2 sub ExprTag a -> E Void2 sub ExprTag b
--pattern SubtypedE n = Subtyped (Dict,Dict,Dict,Dict,Dict) n
pattern SubtypedE n <- Subtyped (Dict,Dict,Dict,Dict,Dict,Dict,Dict) n
  where SubtypedE n  = Subtyped (Dict,Dict,Dict,Dict,Dict,Dict,Dict) n


type instance LambdaX sub ExprTag a b =
  ( Dict ((RValue (E Void2 sub ExprTag) ) b)
  , Dict (SingI a)
  , Dict (SingI b)
  )
pattern LambdaE :: 
  ( RValue (E Void2 sub ExprTag)  b
  , SingI a
  , SingI b
  )
  => Maybe (LensM (AssocCtxMonad ExprTag) (E Void2 sub ExprTag a)) -> E Void2 sub ExprTag b  -> E Void2 sub ExprTag (a ~> b)
pattern LambdaE n m <- Lambda _ n m
  where LambdaE n m = Lambda (Dict,Dict,Dict) n m


type instance AppX sub ExprTag f x arg b = 
  ( Dict (((~) (RValueT f)) (arg ~> b))
  , Dict (((~) (UpperBound (RValueT x) arg)) (Just arg))
  , Dict (SingI f)
  , Dict (SingI x)
  , Dict (SingI arg)
  , Dict (SingI b)
  , Dict (TypesCaseAnalysis (RValue (E Void2 sub ExprTag)))
  , Dict (AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub))

  )
pattern AppE :: forall sub b. 
  ( SingI b
  , TypesCaseAnalysis (RValue (E Void2 sub ExprTag))
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)
  ) => forall f x arg . 
      ( RValueT f ~ (arg ~> b)
      , UpperBound (RValueT x) arg ~ Just arg
      , SingI f
      , SingI x
      , SingI arg
      ) => E Void2 sub ExprTag f -> E Void2 sub ExprTag x -> E Void2 sub ExprTag b
pattern AppE f x = App (Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict) f x
--pattern AppE f x <- App _ f x
--  where AppE f x = App (Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict) f x 


type instance IfX sub ExprTag x0 x1 x2 x3 = 
  ( Dict (TypesCaseAnalysis (RValue (E Void2 sub ExprTag)))
  , Dict (AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub))
  , Dict ( RValueT x0 ~ Value Z)
  , Dict ( ((~) (UpperBound (RValueT x1) (RValueT x2))) (Just x3))
  , Dict ( SingI x0)
  , Dict ( SingI x1)
  , Dict ( SingI x2)
  , Dict ( SingI x3)
  )
pattern IfE :: forall sub x3. (SingI x3) => forall x0 x1 x2. 
  ( TypesCaseAnalysis (RValue (E Void2 sub ExprTag))
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)
  , RValueT x0 ~ Value Z
  , UpperBound (RValueT x1) (RValueT x2) ~ Just x3
  , SingI x1
  , SingI x2
  , SingI x0
  ) => E Void2 sub ExprTag x0 -> E Void2 sub ExprTag x1 -> E Void2 sub ExprTag x2 -> E Void2 sub ExprTag x3
pattern IfE x0 x1 x2 <- If (Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict) x0 x1 x2
  where IfE x0 x1 x2 = If (Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict) x0 x1 x2

type instance ExpX sub ExprTag a = 
  ( sub a
  , Dict (TypesCaseAnalysis (RValue sub))
  , Dict (AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub))
  )

pattern ExpE :: forall sub a. 
  ( TypesCaseAnalysis (RValue sub)
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)
  ) => sub a -> E Void2 sub ExprTag a
pattern ExpE x0  <- Exp (x0,Dict,Dict)
  where ExpE x0  = Exp (x0,Dict,Dict)

instance 
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  ) => RValue (E Void2 sub ExprTag)  (Value a) where
  type RVCtx (E Void2 sub ExprTag) = ExprTag
  rvalue (Val n)                        = pure (Val n)
  rvalue (ValueC (Dict,e) gamma)        = localM (pure . const gamma) $ rvalue e
  rvalue (LambdaC Dict gamma)           = pure $ LambdaCE gamma
  rvalue (Lambda (Dict,Dict,Dict) x t)  = do
    gamma <- ask
    pure $ LambdaCE (gamma,x,t)
  rvalue e@(App {})          = genRVApp e
  rvalue v@(Var {})          = genRVVar v
  rvalue e@(Closure {})      = genRVClosure e
  rvalue e@(Subtyped {})     = genRVSubtyped   e
  rvalue e@(If {})           = genRVIf e
  rvalue (Exp (v,Dict,Dict)) = ExpE <$> rvalue v 
  

instance  
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  ) => RValue (E Void2 sub ExprTag) (Lazy a) where

    type RVCtx (E Void2 sub ExprTag) = ExprTag

    rvalue (Defer (Dict,Dict,Dict) v) = genRVDefer (DeferE v)
    rvalue e@(App {})        = genRVApp e
    rvalue e@(Closure {})    = genRVClosure e
    rvalue v@(Var {})        = genRVVar v
    rvalue (Formula _ e)     = cvalue e
    rvalue e@(Subtyped {})   = genRVSubtyped e
    rvalue e@(If {})  = genRVIf e
    rvalue (Exp (v,Dict,Dict)) = ExpE <$> rvalue  v 
    rvalue _ = undefined


instance 
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  ) => RValue (E Void2 sub ExprTag) (Zilly.Types.Array a) where

  type RVCtx (E Void2 sub ExprTag) = ExprTag

  rvalue (Exp (v,Dict,Dict)) = ExpE <$> rvalue v 
  rvalue v@(Var {})          = genRVVar v
  rvalue e@(If {})           = genRVIf e
  rvalue e@(Closure {})      = genRVClosure e
  rvalue e@(Subtyped {})     = genRVSubtyped   e
  rvalue e@(App {})          = genRVApp e
  rvalue (ValueC (_,e) gamma) = localM (pure . const gamma) $ rvalue e
  rvalue (Val n)              = pure (Val n)

instance
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  ) => RValue (E Void2 sub ExprTag) (LazyS a) where

  type RVCtx (E Void2 sub ExprTag) = ExprTag

  rvalue (Exp (v,Dict,Dict)) = ExpE <$> rvalue v
  rvalue v@(Var {})        = genRVVar v
  rvalue e@(If {})         = genRVIf e
  rvalue e@(Closure {})    = genRVClosure e
  rvalue e@(Subtyped {})   = genRVSubtyped   e
  rvalue e@(App {})        = genRVApp e
  rvalue (ValueC (_,e) gamma)  = localM (pure . const gamma) $ rvalue e
  rvalue (Val n)               = pure (Val n)


------------------------------
-- Generic R-Value Functions
------------------------------

genRVar :: 
  ( MonadIO (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  , RValue (E Void2 sub ExprTag) a
  , RValueT a ~ c
  ) => E Void2 sub ExprTag a -> (AssocCtxMonad ExprTag) (E Void2 sub ExprTag c)
genRVar (VarE x) = rvalue <=< cvalue $ x
genRVar _ = undefined

genRVIf ::forall {x4 :: Types} {m :: Type -> Type} (x3 :: Types) sub .
  ( RValueT x3 ~ x4
  , AssocCtxMonad ExprTag ~ m
  , MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  )
  => E Void2 sub ExprTag x3 -> m (E Void2 sub ExprTag x4)
genRVIf (If @_ @_ @(x0 :: Types) @(x1 :: Types) @(x2 :: Types) (Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict) cond t f) 
  = withSingIRType @x1
  $ withSingIRType @x2
  $ withRVType @(E Void2 sub ExprTag) (sing @x0)
  $ withRVType @(E Void2 sub ExprTag) (sing @x1)
  $ withRVType @(E Void2 sub ExprTag) (sing @x2)
  $ withRVType @(E Void2 sub ExprTag) (sing @x3)
  $ rvalue cond >>= \case
    ValE (connector -> True) -> do 
      t' <- rvalue t
      withSingIRType @x3 $ case upcast  @_ @_ @x4  UpcastE t' of
        SameTypeUB t'' -> pure t''
        RightUB t'' -> pure t''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    ValE (connector -> False) -> do 
      f' :: E Void2 sub ExprTag c1 <- rvalue f
      withSingIRType @x3 $ case upcast  @_ @_ @x4 UpcastE f' of
        SameTypeUB f'' -> pure f''
        RightUB f'' -> pure f''
        LeftUB _ -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
        NonExistentUB -> error "impossible case"
    c' -> rvalue (IfE c' t f)
genRVIf _ = undefined

genRVApp :: forall sub b.
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
  ) => E Void2 sub ExprTag b -> (AssocCtxMonad ExprTag) (E Void2 sub ExprTag (RValueT b))
genRVApp (App @_ @_ @f @x @_ @arg (Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict) f a) 
  = withRVType @(E Void2 sub ExprTag) (sing @f) 
  $ withRVType @(E Void2 sub ExprTag) (sing @x)
  $ withRVType @(E Void2 sub ExprTag) (sing @b)
  $ rvalue f >>= \case
    LambdaC _ (gamma, x, t) -> withSingIRType @x  $ do
      arg <- rvalue a >>= \rva -> case upcast @_  @_ @arg UpcastE rva of
        SameTypeUB rva'   -> pure rva'
        RightUB rva'      -> pure rva'
        -- these two can only happen when the types are equal
        -- but I have yet to find a stricter constraint that expresses this.
        LeftUB _          -> error "impossible case"
        SomethingElseUB _ -> error "impossible case"
      case x of 
        Just x' -> do 
          t'  <- localM (setMF x' arg . const gamma) $ rvalue t
          gamma' <- setMF x' arg gamma
          pure $ ClosureE  (t',gamma')
        Nothing -> (\t' -> ClosureE (t',gamma)) <$>  rvalue t
    f' ->   rvalue $ AppE f' a
genRVApp _ = undefined

genRVDefer :: 
  ( RValue (E Void2 sub ExprTag) a
  , SingI a
  , SingI (RValueT a)
  , MonadReader (Gamma (AssocCtxMonad ExprTag)) m
  ) => E Void2 sub ExprTag (Lazy a) -> m (E Void2 sub ExprTag a)
genRVDefer (DeferE v) = do
  gamma <- ask 
  pure $ ClosureE (v,gamma)
genRVDefer _ = undefined

genRVClosure :: 
  ( MonadReader (Gamma (AssocCtxMonad ctx)) (AssocCtxMonad ctx)
  , RValue (E Void2 sub ctx) a
  , RVCtx (E Void2 sub ctx) ~ ctx
  ) => E Void2 sub ctx a -> AssocCtxMonad ctx (E Void2 sub ctx (RValueT a))
genRVClosure (Closure _ (e,gamma)) = localM (pure . const gamma) $ rvalue e
genRVClosure _  = undefined


genRVVar :: 
  ( RValue (E Void2 sub ctx) a
  , MonadReader (Gamma (AssocCtxMonad ctx)) (AssocCtxMonad ctx)
  , RVCtx (E Void2 sub ctx) ~ ctx
  ) => E Void2 sub ctx a -> AssocCtxMonad ctx (E Void2 sub ctx (RValueT a))
genRVVar (Var _ x) = rvalue <=< cvalue $ x
genRVVar _ = undefined

genRVSubtyped ::
  ( MonadIO (AssocCtxMonad ExprTag)
  , Alternative (AssocCtxMonad ExprTag)
  ) => E Void2 sub ExprTag b -> (AssocCtxMonad ExprTag) (E Void2 sub ExprTag (RValueT b))
genRVSubtyped (Subtyped @_ @_ @e1 @e2 (Dict,Dict,Dict,Dict,Dict,Dict,Dict) e1) = do
    --trace "rvaluing a subtyped" pure ()
    e1' :: E Void2 sub ExprTag (RValueT  e1)  <- withSingIRType @e1 $ rvalue e1
    let e1'' :: E Void2 sub ExprTag (RValueT e2) 
          = withRVType @(E Void2 sub ExprTag)  (sing @e1) 
          $ withSingIRType @e1
          $ withSingIRType @e2
          $ withRVType @(E Void2 sub ExprTag) (sing @(RValueT e1)) 
          $ withRVType @(E Void2 sub ExprTag) (sing @(RValueT e2)) 
          $ rvaluePreservesST @(RValueT e1) @e2 
          $ SubtypedE e1'
    pure e1''
genRVSubtyped _ = undefined

------------------------------
-- How ExprTag upcasts.
------------------------------

type instance UpcastX (E Void2 sub ExprTag) a  = 
  ( Dict (SingI a)
  , Dict (TypesCaseAnalysis (RValue (E Void2 sub ExprTag)))
  , Dict (AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub))
  )
pattern UpcastE :: forall a  sub.
  ( SingI a 
  , TypesCaseAnalysis (RValue (E Void2 sub ExprTag))
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)

  ) => UpcastX (E Void2 sub ExprTag) a 
pattern UpcastE  <- (Dict,Dict,Dict)
  where UpcastE  =  (Dict,Dict,Dict)


instance Upcast (E  Void2 sub ExprTag) where
  upcast :: forall a b . SingI b 
    => UpcastX (E Void2 sub ExprTag) a  -> E Void2 sub ExprTag a -> UpperBoundResults (E Void2 sub ExprTag) a b
  upcast (Dict,Dict,Dict) f 
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
              $ withRVType @(E Void2 sub ExprTag) (sing @a) 
              $ withRVType @(E Void2 sub ExprTag) (sing @b) 
              $ RightUB (SubtypedE f)
            Nothing   
              -> withRVType @(E Void2 sub ExprTag) (sing @a) 
              $ withSingI sub
              $ withRVType @(E Void2 sub ExprTag)  (sing @n) 
              $ subtyped'CTX @(E Void2 sub ExprTag) @a @b   
              $ SomethingElseUB (SubtypedE f)
        SNothing  -> NonExistentUB


---------------------------
-- Show instances
---------------------------

instance (Monad m) => ShowM m (E Void2 sub ExprTag a) where
  showsPrecM p = \case
    Val  (_,n,Dict) -> showStringM (show n)
    ValueC  (_,e) _ -> showStringM "<" <=< showStringM "," <=< showsPrecM p e <=< showStringM ">" -- showStringM "<" <=< showsPrecM 10 env <=< showStringM "," <=< showsPrecM p e <=< showStringM ">"
    Var _ x -> showsPrecM p . UT . varNameM $ x
    If _ c t f -> showParenM (p > 10) $ showStringM "if " <=< showsM c <=< showStringM " then " <=< showsM t <=< showStringM " else " <=< showsM f
    Lambda _ x t -> showParenM (p > 9) $ showStringM "λ " <=< showsPrecM 10 (UT $ maybe "" varNameM  x) <=< showStringM " -> " <=<  showsPrecM 0 t
    LambdaC _ (_,x,t) -> showParenM (p > 9) $  showStringM "λ " <=< showsPrecM 10 (UT $ maybe "" varNameM x) <=< showStringM " -> " <=< showsPrecM 10 t -- -> showParenM (p > 9) $ showsPrecM 10 env <=<  showStringM "λ " <=< showsPrecM 10 (UT . varNameM $ x) <=< showStringM " -> " <=< showsPrecM 10 t
 
    App _ f a -> showParenM (p > 10) $ showsPrecM 10 f <=< showCharM ' ' <=< showsPrecM 11 a
    Defer _ v -> showStringM "'" <=< showsPrecM 11 v <=< showStringM "'"
    Closure _ (e,_) -> showsPrecM 10 e -- showCharM '<' <=< showsPrecM 10 e <=< showStringM  ", " <=< showsPrecM 10 env <=< showCharM '>'
    Formula _ e -> showStringM "Formula " <=< (showsPrecM 11 . UT . varNameM) e
    -- FEval  _ -> undefined
    -- DeferS _ -> undefined
    Subtyped _ e -> showStringM "Subtyped " <=< showsPrecM 10 e
    Exp _ -> showStringM "no additional extensions"
