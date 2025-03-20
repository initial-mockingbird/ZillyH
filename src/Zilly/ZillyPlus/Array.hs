{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE LambdaCase                 #-}
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
module Zilly.ZillyPlus.Array where

import Data.Proof
import Utilities.LensM
import Utilities.TypedMapPlus
import Zilly.Types
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Array 
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter
import Zilly.ZillyPlus.Expression

import Data.Foldable
import Control.Monad 

import Control.Applicative

import Utilities.ShowM
import Prelude hiding (LT,GT,EQ)
import Prelude.Singletons (SingI(..),Sing,SMaybe(..),withSingI)
import Data.Sequence 


--------------------------
-- Util functions 
--------------------------

collapseArray :: forall sup sub a. ArrayE sup sub ArrayTag  a 
  -> (AssocCtxMonad ArrayTag) (ArrayE sup sub ArrayTag a)
collapseArray (ArrayIndex (f ,Dict) (ArrayLiteral (Dict,Dict) xs) ix) 
  = index xs <$> f ix  
collapseArray (ArrayIndex (f,Dict) ai ix) = do 
  ai' <- collapseArray ai 
  collapseArray (ArrayIndex (f,Dict) ai' ix)
collapseArray a = pure a


------------------------
-- Types and instances- 
------------------------


data ArrayTag


type instance AssocCtxMonad ArrayTag = TaggedInterpreter ExprTag


type instance ArrayLiteralX sup sub ArrayTag a = 
  ( Dict (TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag)))
  , Dict (SingI a)
  )
pattern ArrayLiteralE :: forall sup sub a. 
  ( SingI a 
  , TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag))

  ) => Seq (ArrayE sup sub ArrayTag a) -> ArrayE sup sub ArrayTag (Array a)
pattern ArrayLiteralE xs <- ArrayLiteral (Dict,Dict) xs 
  where ArrayLiteralE xs  = ArrayLiteral (Dict,Dict) xs

type instance ArrayIndexX sup sub ArrayTag a = 
  (  ArrayE sup sub ArrayTag (Value Z) -> (AssocCtxMonad ArrayTag) Int
  , Dict (TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag)))

  )
pattern ArrayIndexE :: forall sup sub a. 
  ( TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag))
  ) => (ArrayE sup sub ArrayTag (Value Z) -> (AssocCtxMonad ArrayTag) Int) 
    -> ArrayE sup sub ArrayTag (Array a)
    -> ArrayE sup sub ArrayTag (Value Z)
    -> ArrayE sup sub ArrayTag a
pattern ArrayIndexE f xs ix <- ArrayIndex (f,Dict) xs ix
  where ArrayIndexE f xs ix = ArrayIndex (f,Dict) xs ix 
 
type instance ArrayInhX sup sub ArrayTag a = 
  ( sup a 
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (AssocCtxMonad ArrayTag ~ AssocCtxMonad (RVCtx sup))
  )
pattern ArrayInhE :: forall sup sub a. 
  ( TypesCaseAnalysis (RValue sup)
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sup)
  ) => sup a -> ArrayE sup sub ArrayTag a
pattern ArrayInhE x0  <- ArrayInh (x0,Dict,Dict)
  where ArrayInhE x0   = ArrayInh (x0,Dict,Dict)


type instance ArrayExpX sup sub ArrayTag a = 
  ( sub a 
  , Dict (TypesCaseAnalysis (RValue sub))
  , Dict (AssocCtxMonad ArrayTag ~ AssocCtxMonad (RVCtx sub))
  )
pattern ArrayExpE :: forall sup sub a. 
  ( TypesCaseAnalysis (RValue sub)
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)
  ) => sub a -> ArrayE sup sub ArrayTag a
pattern ArrayExpE x0  <- ArrayExp (x0,Dict,Dict)
  where ArrayExpE x0   = ArrayExp (x0,Dict,Dict)

instance RValue (ArrayE sup sub ArrayTag) (Value a) where
  type RVCtx (ArrayE sup sub ArrayTag) = ArrayTag  
  rvalue (ArrayExp (v,Dict,Dict)) = ArrayExpE <$> rvalue v
  rvalue (ArrayInh (v,Dict,Dict)) = ArrayInhE <$> rvalue v
  rvalue ai@(ArrayIndex {}) = collapseArray ai >>= rvalue
  

instance RValue (ArrayE sup sub ArrayTag) (Lazy a) where
  type RVCtx (ArrayE sup sub ArrayTag) = ArrayTag  
  rvalue (ArrayExp (v,Dict,Dict)) = ArrayExpE <$> rvalue v
  rvalue (ArrayInh (v,Dict,Dict)) = ArrayInhE <$> rvalue v
  rvalue ai@(ArrayIndex {}) = collapseArray ai >>= rvalue

instance RValue (ArrayE sup sub ArrayTag) (LazyS a) where
  type RVCtx (ArrayE sup sub ArrayTag) = ArrayTag  
  rvalue (ArrayExp (v,Dict,Dict)) = ArrayExpE <$> rvalue v
  rvalue (ArrayInh (v,Dict,Dict)) = ArrayInhE <$> rvalue v
  rvalue ai@(ArrayIndex {}) = collapseArray ai >>= rvalue

instance RValue (ArrayE sup sub ArrayTag) (Zilly.Types.Array a) where
  type RVCtx (ArrayE sup sub ArrayTag) = ArrayTag  
  rvalue (ArrayLiteral (Dict,Dict) xs) 
    = withRVType @(ArrayE sup sub ArrayTag) (sing @a) 
    $ withSingIRType @a 
    $ ArrayLiteral (Dict,Dict) <$> traverse rvalue xs
  rvalue (ArrayExp (v,Dict,Dict)) = ArrayExpE <$> rvalue v
  rvalue (ArrayInh (v,Dict,Dict)) = ArrayInhE <$> rvalue v
  rvalue ai@(ArrayIndex {}) = collapseArray ai >>= rvalue

data Exists f where
  MkExists ::  (forall (x :: Types). Sing x -> UpcastX f x)  -> Exists f



type instance UpcastX (ArrayE sup sub ArrayTag) a  =
  ( Exists sup 
  , Exists sub
  , Dict (Upcast sup)
  , Dict (Upcast sub)
  , Dict (SingI a)
  -- , Dict (TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag)))
  -- , Dict (TypesCaseAnalysis (RValue sup))
  -- , Dict (TypesCaseAnalysis (RValue sub))
    )
pattern UpcastArrayE :: forall sup sub a . 
  ( Upcast sup 
  , Upcast sub
  , SingI a
  -- , TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag))
  -- , TypesCaseAnalysis (RValue sup)
  -- , TypesCaseAnalysis (RValue sub)
 ) => Exists sup  -> Exists sub  ->  UpcastX (ArrayE sup sub ArrayTag) a  
pattern UpcastArrayE sup sub  <- (sup,sub,Dict,Dict,Dict)
  where UpcastArrayE sup sub   = (sup,sub,Dict,Dict,Dict)

-- pattern UpcastArrayE sup sub  <- (sup,sub,Dict,Dict,Dict,Dict,Dict,Dict)
--   where UpcastArrayE sup sub   = (sup,sub,Dict,Dict,Dict,Dict,Dict,Dict)



-- type instance UpcastX (ArrayE sup sub ArrayTag) (f a)  =
--   ( UpcastX sup a  
--   , UpcastX sub a
--   , Dict (Upcast sup)
--   , Dict (Upcast sub)
--   , Dict (SingI a)
--   , Dict (TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag)))
--   , Dict (TypesCaseAnalysis (RValue sup))
--   , Dict (TypesCaseAnalysis (RValue sub))
--   )

-- type instance UpcastX (ArrayE sup sub ArrayTag) a  =
--   ( UpcastX sup a  
--   , UpcastX sub a
--   , Dict (Upcast sup)
--   , Dict (Upcast sub)
--   , Dict (SingI a)
--   , Dict (TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag)))
--   , Dict (TypesCaseAnalysis (RValue sup))
--   , Dict (TypesCaseAnalysis (RValue sub))
--   )
-- pattern UpcastArrayE :: forall sup sub a . 
--   ( Upcast sup 
--   , Upcast sub
--   , SingI a
--   , TypesCaseAnalysis (RValue (ArrayE sup sub ArrayTag))
--   , TypesCaseAnalysis (RValue sup)
--   , TypesCaseAnalysis (RValue sub)
--  ) => UpcastX sup a -> UpcastX sub a -> UpcastX (ArrayE sup sub ArrayTag) (Array a)  
-- pattern UpcastArrayE sup sub <- (sup,sub,Dict,Dict,Dict,Dict,Dict,Dict)
--   where UpcastArrayE sup sub  = (sup,sub,Dict,Dict,Dict,Dict,Dict,Dict)
--


-- instance 
--   ( Upcast sup
--   , Upcast sub
--   ) => Upcast (ArrayE sup sub ArrayTag) where
--   upcast :: forall (a :: Types) (b :: Types)  
--      . SingI b 
--      => UpcastX (ArrayE sup sub ArrayTag) a  
--      ->  ArrayE sup sub ArrayTag a  
--      -> UpperBoundResults (ArrayE sup sub ArrayTag) a b
--   upcast 
--     ds (ArrayLiteral @_ @_ @_ @a1 (Dict,Dict) (x :<| xs) ) 
--     = case (sing @a,ds) of 
--     (SArray _, (sup,sub,Dict,Dict,Dict,Dict,Dict,Dict)) ->  case sing @b of
--       SLazy _ -> withSingIUBType @a @b $ case sing @(UpperBound a b) of
--         SNothing -> NonExistentUB 
--       SLazyS _ -> withSingIUBType @a @b $ case sing @(UpperBound a b) of
--         SNothing -> NonExistentUB 
--       SValue _ -> withSingIUBType @a @b $ case sing @(UpperBound a b) of
--         SNothing -> NonExistentUB 
--       SArray @sb sb -> withSingI sb $ case upcast @_ @_ @(Array sb) ds (ArrayLiteralE xs) of
--         NonExistentUB -> NonExistentUB 
--         SameTypeUB  xs' -> SameTypeUB . ArrayLiteralE $ x :<| xs
--         LeftUB xs'      -> LeftUB . ArrayLiteralE $ x :<| xs
--         RightUB (ArrayLiteralE @_ @_ @bElem xs') ->  case upcast @_ @_ @bElem (UpcastArrayE sup sub) x of
--           SameTypeUB x'    -> SameTypeUB . ArrayLiteralE $ x' :<| xs'
--           LeftUB x'        -> LeftUB . ArrayLiteralE $ x' :<| xs'
--           RightUB x'       -> RightUB . ArrayLiteralE $ x' :<| xs'
--           SomethingElseUB x' -> SomethingElseUB . ArrayLiteralE $ x' :<| xs'
--
--         SomethingElseUB (ArrayLiteral @_ @_ @ctx @bElem (Dict,Dict) xs') 
--           -> ubIsInjective @Array @(Array a1) @(Array sb)
--             $ case upcast @_ @a1 @sb UpcastArrayE x of 
--               SomethingElseUB x' -> SomethingElseUB . ArrayLiteralE $ x' :<| xs'
--               SameTypeUB x' -> SomethingElseUB . ArrayLiteralE $ x' :<| xs'
--               LeftUB x' -> SomethingElseUB . ArrayLiteralE $ x' :<| xs'
--               RightUB x' -> SomethingElseUB . ArrayLiteralE $ x' :<| xs'
--         _ -> error "impossible case"
--   upcast ds@(Dict,Dict,Dict,Dict,Dict,Dict) (ArrayInh (v,Dict,Dict))
--     = withRVType @sup (sing @b)
--     $ case upcast @sup @a @b (sing @a) v of
--       NonExistentUB -> undefined 
--       SameTypeUB v' -> undefined 
--       LeftUB v' -> undefined 
--       RightUB v' -> undefined 
--       SomethingElseUB v' -> undefined
--   upcast _ _ = undefined
--     
--
--
--









instance Upcast (ArrayE sup sub ArrayTag) where
   upcast :: forall (a :: Types) (b :: Types)  
     . SingI b 
     => UpcastX (ArrayE sup sub ArrayTag) a  
     ->  ArrayE sup sub ArrayTag a  
     -> UpperBoundResults (ArrayE sup sub ArrayTag) a b
   upcast 
     -- (MkExists supFactory,MkExists subFactory,Dict,Dict,Dict,Dict,Dict,Dict) 
     (MkExists supFactory,MkExists subFactory,Dict,Dict,Dict) 
     (ArrayLiteral @_ @_ @_ @a1 (Dict,Dict) xs ) 
     = case upcastable @a @b @ArrayE @sup @sub @ArrayTag of
       NonExistentUB -> NonExistentUB
       SameTypeUB _  -> SameTypeUB (ArrayLiteral (Dict,Dict) xs)
       LeftUB     _  -> LeftUB     (ArrayLiteral (Dict,Dict) xs)
       RightUB    _  -> case (sing @b,sing @a) of
         (SArray  @b1 b1,SArray _) -> withSingI b1 $
               let 
                     xs0  :: Seq (UpperBoundResults (ArrayE sup sub ArrayTag) a1 b1) 
                             = upcast @(ArrayE sup sub ArrayTag) @a1 @b1 
                               ( MkExists supFactory
                               , MkExists subFactory 
                               , Dict 
                               , Dict 
                               , Dict 
                               -- , Dict 
                               -- , Dict 
                               -- , Dict
                               )
                               <$> xs 
                     xs1 :: Seq (ArrayE sup sub ArrayTag b1) = (\(RightUB a) -> a) <$> xs0 

                     xs2 :: ArrayE sup sub ArrayTag (Array b1) 
                       = ArrayLiteral 
                         ( Dict
                         , Dict
                         ) xs1
                     
                     x3 :: UpperBoundResults (ArrayE sup sub ArrayTag) a b 
                       = RightUB xs2
               in x3
       SomethingElseUB _ -> case (sing @b,sing @a ) of
         (SArray  @b1 b1,SArray _) 
           -> withSingI b1 
           $ withSingIUBType @a1 @b1
           $ case sing @(UpperBound a1 b1) of 
             SJust @_ @r sr -> withSingI sr $
               let 
                     xs0  :: Seq (UpperBoundResults (ArrayE sup sub ArrayTag) a1 b1) 
                             = upcast @(ArrayE sup sub ArrayTag) @a1 @b1 
                               ( MkExists supFactory
                               , MkExists subFactory 
                               , Dict 
                               , Dict 
                               , Dict 
                               -- , Dict 
                               -- , Dict 
                               -- , Dict
                               )
                               <$> xs 
                     xs1 :: Seq (ArrayE sup sub ArrayTag r) = (\(SomethingElseUB a) -> a) <$> xs0 

                     xs2 :: ArrayE sup sub ArrayTag (Array r) 
                       = ArrayLiteral 
                         ( Dict
                         , Dict
                         ) xs1
                     
                     x3 :: UpperBoundResults (ArrayE sup sub ArrayTag) a b 
                       = SomethingElseUB xs2
               in x3


   -- upcast (MkExists supX,_,Dict,Dict,Dict,Dict,Dict,Dict) (ArrayInh (v,Dict,Dict))
   upcast (MkExists supX,_,Dict,Dict,Dict) (ArrayInh (v,Dict,Dict))

     = withRVType @sup (sing @b)
     $ case upcast @sup @a @b (supX  $ sing @a ) v of
       NonExistentUB        -> NonExistentUB
       SameTypeUB      supA -> SameTypeUB (ArrayInh (supA,Dict,Dict))
       LeftUB          supA -> LeftUB (ArrayInh (supA,Dict,Dict))
       RightUB         supA -> RightUB (ArrayInh (supA,Dict,Dict))
       SomethingElseUB supA -> case sing @(UpperBound a b) of
         SJust (SValue _) -> SomethingElseUB (ArrayInh (supA,Dict,Dict))
         SJust (SLazy _) -> SomethingElseUB (ArrayInh (supA,Dict,Dict))
         SJust (SLazyS _) -> SomethingElseUB (ArrayInh (supA,Dict,Dict))
         SJust (SArray _) -> SomethingElseUB (ArrayInh (supA,Dict,Dict))

   -- upcast (_,MkExists subX,Dict,Dict,Dict,Dict,Dict,Dict) (ArrayExp (v,Dict,Dict))
   upcast (_,MkExists subX,Dict,Dict,Dict) (ArrayExp (v,Dict,Dict))

     = withRVType @sub (sing @b)
     $ case upcast @sub @a @b (subX $ sing @a) v of
       NonExistentUB        -> NonExistentUB
       SameTypeUB      supA -> SameTypeUB (ArrayExp (supA,Dict,Dict))
       LeftUB          supA -> LeftUB (ArrayExp (supA,Dict,Dict))
       RightUB         supA -> RightUB (ArrayExp (supA,Dict,Dict))
       SomethingElseUB supA -> case sing @(UpperBound a b) of
         SJust (SValue _) -> SomethingElseUB (ArrayExp (supA,Dict,Dict))
         SJust (SLazy _) -> SomethingElseUB (ArrayExp (supA,Dict,Dict))
         SJust (SLazyS _) -> SomethingElseUB (ArrayExp (supA,Dict,Dict))
         SJust (SArray _) -> SomethingElseUB (ArrayExp (supA,Dict,Dict))

   upcast  
     -- (MkExists supX,MkExists subX,Dict,Dict,Dict,Dict,Dict,Dict) 
     (MkExists supX,MkExists subX,Dict,Dict,Dict) 
     (ArrayIndex @_ @_ @_ @a1 v xs ix)
     -- = case upcast @(ArrayE sup sub ArrayTag) @(Array a1) @(Array b) (MkExists supX,MkExists subX,Dict,Dict,Dict,Dict,Dict,Dict) xs of 
     = case upcast @(ArrayE sup sub ArrayTag) @(Array a1) @(Array b) (MkExists supX,MkExists subX,Dict,Dict,Dict) xs of 

       NonExistentUB        -> ubIsInjective' @Array @a1 @b $ NonExistentUB
       SameTypeUB      supA -> ubIsInjective  @Array @a1 @b $ SameTypeUB  (ArrayIndex v supA ix)
       LeftUB          supA -> ubIsInjective  @Array @a1 @b $ LeftUB  (ArrayIndex v supA ix) 
       RightUB         supA -> ubIsInjective  @Array @a1 @b $ RightUB (ArrayIndex v supA ix) 
       SomethingElseUB supA -> withSingIUBType @a @b $ case sing @(UpperBound a b) of
         SJust (SValue a) -> withSingI a $ ubIsInjective  @Array @a1 @b $ SomethingElseUB (ArrayIndex v supA ix) 
         SJust (SLazy a)  -> withSingI a $ ubIsInjective  @Array @a1 @b $ SomethingElseUB(ArrayIndex v supA ix) 
         SJust (SLazyS a) -> withSingI a $ ubIsInjective  @Array @a1 @b $ SomethingElseUB (ArrayIndex v supA ix) 
         SJust (SArray a) -> withSingI a $ ubIsInjective  @Array @a1 @b $ SomethingElseUB (ArrayIndex v supA ix) 
  


instance 
  ( Monad m
  , C (ShowM m) sup
  , C (ShowM m) sub
  ) => ShowM m (ArrayE sup sub ArrayTag a) where 
  showsPrecM p = \case 
    ArrayLiteral _ (x :<| xs) 
      -> showCharM '[' 
      <=< foldl' (\acc  x' -> acc <=< showStringM  ", " <=< showsM x') (showsM x) xs 
      <=< showCharM ']'
    ArrayLiteral _  Empty -> showStringM "[]" 
    ArrayIndex _ ai ix -> showParenM (p > 10) 
      $ showsPrecM 10 ai <=< showCharM '[' <=< showsM ix <=< showCharM ']' 
    ArrayInh (x,_,Dict) -> showsPrecM p x
    ArrayExp (x,_,Dict) -> showsPrecM p x


