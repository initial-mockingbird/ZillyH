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
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module Zilly.Classic.ADT.TypeCheck where

import Zilly.Classic.Newtypes
import Zilly.Classic.ADT.Action 
import Zilly.Classic.ADT.Expression
import Zilly.Classic.Parser hiding (Types(..), mkVar,A1(..),A0(..)) 
import Zilly.Classic.Parser qualified as ZP
import Data.Map qualified as M
import Data.Map (Map)
import GHC.TypeLits.Singletons
import Control.Monad.Reader 
import Control.Monad.Except
import Control.Monad.Writer.Strict 
import Zilly.Classic.Environment.TypedMap 
import Data.Maybe
import Data.Singletons (SomeSing(..),SingI(..),sing,demote, withSingI, toSing)
import Control.Applicative (Alternative(..))
import Data.Singletons.TH ((:~:)(..))
import Debug.Trace (trace) 
import Data.List.Singletons hiding (Map)

data TypeCheckEnv m = TCE 
  { getGamma     :: Map String Types -- ^ Maps variables to their ltypes 
  , getCValues   :: Map String (SomeExpression m)
  , expectedType :: Maybe Types 
  }

data TypeCheckError 
  = FromGammaError' GammaErrors 
  | TypeMismatch' ExpectedType ActualType
  | NonImplementedFeature String
  | CustomError' String

typeCheckExpr :: forall n m w. 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  , SingI n
  ) 
  => EPrec ParsingStage n -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckExpr e = case 
  ( decideEquality' @n @Atom
  , decideEquality' @n @PrefixPrec
  , decideEquality' @n @PostfixPrec
  , decideEquality' @n @8 
  , decideEquality' @n @7
  , decideEquality' @n @6
  , decideEquality' @n @4
  , decideEquality' @n @1
  , decideEquality' @n @0
  ) of 
    (Just Refl,_,_,_,_,_,_,_,_) -> typeCheckAtom e
    (_,Just Refl,_,_,_,_,_,_,_) -> typeCheckPrefixPrec e
    (_,_,Just Refl,_,_,_,_,_,_) -> typeCheckPostfixPrec e
    (_,_,_,Just Refl,_,_,_,_,_) -> typeCheckP8 e
    (_,_,_,_,Just Refl,_,_,_,_) -> typeCheckP7 e
    (_,_,_,_,_,Just Refl,_,_,_) -> typeCheckP6 e
    (_,_,_,_,_,_,Just Refl,_,_) -> typeCheckP4 e
    (_,_,_,_,_,_,_,Just Refl,_) -> typeCheckP1 e
    (_,_,_,_,_,_,_,_,Just Refl) -> typeCheckP0 e
    _ -> error "impossible case typeCheckExpr"

typeCheckAtom :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage Atom -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckAtom (PInt bk n) = do 
  env <- ask 
  case expectedType env of 
    Just Z -> pure (MkSomeExpression . Val $ n, Z)
    Just t -> case toSing t of 
      SomeSing @_ @st st -> withSingI st $ case upcastable @st @(PZ) of 
        SameTypeUB _ -> pure (MkSomeExpression . Val $ n, Z)
        LeftUB _ -> eqWeakening @(UpperBound st (PZ)) @(Just st) $ 
          pure (MkSomeExpression . Subtyped @st . Val $ n, t)
        _ -> do 
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t) (ActualType . show $ Z) ) 
          pure (MkSomeExpression . Val $ n, Z)
    Nothing -> pure (MkSomeExpression . Val $ n, Z)
typeCheckAtom (PDouble bk _) = do  
  (tell . pure)  (bk, NonImplementedFeature "Floating Point type")
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckAtom (PBool bk _) = do  
  (tell . pure)  (bk, NonImplementedFeature "Boolean type")
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckAtom (PVar bk x) = do
  env <- ask 
  case expectedType env of 
    Just t -> case M.lookup x $ getGamma env of 
      Nothing -> do 
        (tell . pure) (bk, FromGammaError' $ VariableNotDefined x)
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      Just ltype -> case (toSing ltype, toSing t) of 
        (SomeSing @_ @ltype' st', SomeSing @_ @t' t') 
          -> withSingI st' 
          $ withSingI t'
          $ withSingIFtype @ltype' 
          $ case upcastable @t' @(Ftype ltype') of  
            SameTypeUB _ -> pure (MkSomeExpression . Var $ mkVar @ltype' x, ftype ltype )
            LeftUB _ 
              -> eqWeakening @(UpperBound t' (Ftype ltype')) @(Just t')
              $ pure (MkSomeExpression . Subtyped @t' . Var $ mkVar @ltype' x, ftype ltype)
            _ -> do 
              (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t) (ActualType . show . ftype $ ltype))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    Nothing -> case M.lookup x $ getGamma env of 
      Nothing -> do 
        (tell . pure) (bk, FromGammaError' $ VariableNotDefined x)
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      Just ltype -> case toSing ltype of 
        SomeSing @_ @ltype' st' 
          -> withSingI st' 
          $ withSingIFtype @ltype' 
          $ pure (MkSomeExpression . Var $ mkVar @ltype' x, ftype ltype )
typeCheckAtom (PParen _ e) = typeCheckExpr e
typeCheckAtom (PDefer bk e) = do 
  env <- ask 
  case expectedType env of 
    Nothing -> (typeCheckExpr e) >>= \case 
      (MkSomeExpression @t e', _) -> pure (MkSomeExpression . Defer $ e', ftype (demote @t)) 
    Just (Lazy t') -> (local (\env' -> env'{expectedType=Just t'}) $ typeCheckExpr e) >>= \case 
      (MkSomeExpression @t e', _) -> case toSing t' of 
        SomeSing @_ @t'' t'' -> withSingI t'' $ case upcastable @t'' @t of 
          SameTypeUB _ -> pure (MkSomeExpression . Defer $ e', Lazy t') 
          LeftUB _ 
            -> eqWeakening @(UpperBound (PLazy t'') (PLazy t)) @(Just (PLazy t''))
            $ pure (MkSomeExpression . Subtyped @(PLazy t'') . Defer $ e', Lazy t') 
          _ -> do
            (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t') (ActualType . show $ demote @t))
            pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    Just t' -> (local (\env' -> env'{expectedType=Nothing}) $ typeCheckExpr e) >>= \case 
      (MkSomeExpression @t _, _) -> do 
        (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t') (ActualType . show $ demote @t))
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckAtom (PIf bk (c,t,f)) = do 
  env <- ask 
  MkSomeExpression @c' c' <- withExpectedType (Just $ Z) $ fst <$> typeCheckExpr c 
  MkSomeExpression @t' t' <- fst <$> typeCheckExpr t 
  MkSomeExpression @f' f' <- fst <$> typeCheckExpr f 
  
  case expectedType env of 
    Nothing -> case upcastable @t' @f' of 
      SameTypeUB _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil ->  pure (MkSomeExpression $ If c' t' f', demote @t')
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      LeftUB _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil 
            ->  eqIsReflexive @(Just t')
            $ pure (MkSomeExpression $ If c' t' (Subtyped @t' @f'  f'), demote @t')
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      RightUB _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil 
          -> ubIsCommutative' @f' @t'
          $ ubIsCommutative' @t' @f'
          $ eqWeakening @(UpperBound f' t') @(Just f')
          $ pure (MkSomeExpression $ If c' (Subtyped @f' @t'  t') f', demote @f')
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      SomethingElseUB @sm _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil 
          -> ubIsCommutative' @t' @f'
          $ ubIsUb @t' @f' @sm 
          $ ubIsUb @f' @t' @sm
          $ ubIsCommutative' @t' @sm 
          $ ubIsCommutative' @f' @sm
          $ eqIsReflexive @sm
          $ eqWeakening @(UpperBound t' sm) @(Just sm)
          $ eqWeakening @(UpperBound f' sm) @(Just sm)
          $ pure (MkSomeExpression $ If c' (Subtyped @sm @t'  t') (Subtyped @sm @f' f'), demote @sm)
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
   
      NonExistentUB -> do
        (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

    Just et -> case upcastable @t' @f' of 
      SameTypeUB _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil -> 
          case et == demote @t' of
            True -> pure (MkSomeExpression $ If c' t' f', demote @t')
            False -> do 
              (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ et) (ActualType . show $ demote @t'))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      LeftUB _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil 
          -> eqIsReflexive @(Just t')
          $ case et == demote @t' of
            True ->  pure (MkSomeExpression $ If c' t' (Subtyped @t' @f'  f'), demote @t')
            False -> do 
              (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ et) (ActualType . show $ demote @t'))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      RightUB _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil 
          -> ubIsCommutative' @f' @t'
          $ ubIsCommutative' @t' @f'
          $ eqWeakening @(UpperBound f' t') @(Just f')
          $ case et == demote @t' of
            True ->  pure (MkSomeExpression $ If c' (Subtyped @f' @t'  t') f', demote @f')
            False -> do 
              (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ et) (ActualType . show $ demote @f'))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      SomethingElseUB @sm _ -> case sing @c' of 
        STCon (matches @"Z" -> Just Refl) SNil 
          -> ubIsCommutative' @t' @f'
          $ ubIsUb @t' @f' @sm 
          $ ubIsUb @f' @t' @sm
          $ ubIsCommutative' @t' @sm 
          $ ubIsCommutative' @f' @sm
          $ eqIsReflexive @sm
          $ eqWeakening @(UpperBound t' sm) @(Just sm)
          $ eqWeakening @(UpperBound f' sm) @(Just sm)
          $ case et == demote @t' of
              True -> pure (MkSomeExpression $ If c' (Subtyped @sm @t'  t') (Subtyped @sm @f' f'), demote @sm)
              False -> do 
                (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ et) (ActualType . show $ demote @t'))
                pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
        _ -> do
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
   
      NonExistentUB -> do
        (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @c'))
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

typeCheckAtom (PArray bk _) = do 
  (tell . pure) (bk, NonImplementedFeature "Arrays")
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckAtom (PTuple bk a b) = do 
  env <- ask 
  case expectedType env of 
    Nothing -> do 
      MkSomeExpression @a' a' <- fst <$> typeCheckExpr a
      MkSomeExpression @b' b' <- fst <$> typeCheckExpr b 
      pure (MkSomeExpression $ MkTuple a' b', demote @(PTuple a' b'))
    Just (Tuple ta tb) -> case (toSing ta, toSing tb) of 
      (SomeSing @_ @sa sa, SomeSing @_ @sb sb) 
        -> do
        MkSomeExpression @a' a' <- withExpectedType (Just ta) $ fst <$> typeCheckExpr a
        MkSomeExpression @b' b' <- withExpectedType (Just tb) $ fst <$> typeCheckExpr b 
        withSingI sa 
          $  withSingI sb
          $ case (upcastable @sa @a', upcastable @sb @b') of 
            (SameTypeUB _, SameTypeUB _) -> pure (MkSomeExpression $ MkTuple a' b', demote @(PTuple a' b'))
            (LeftUB _, SameTypeUB _) 
              -> eqWeakening @(UpperBound sa a') @(Just sa)
              $ pure (MkSomeExpression $ MkTuple (Subtyped @sa a') b', demote @(PTuple sa b'))
            (SameTypeUB _, LeftUB _) 
              -> eqWeakening @(UpperBound sb b') @(Just sb)
              $ pure (MkSomeExpression $ MkTuple a' (Subtyped @sb b'), demote @(PTuple a' sb))
            (LeftUB _, LeftUB _) 
              -> eqWeakening @(UpperBound sa a') @(Just sa) 
              $ eqWeakening @(UpperBound sb b') @(Just sb)
              $ pure (MkSomeExpression $ MkTuple (Subtyped @sa a') (Subtyped @sb b'), demote @(PTuple sa sb))
            _ -> do
              (tell . pure) (bk, TypeMismatch' (ExpectedType $ show (Tuple ta tb)) (ActualType . show $ demote @(PTuple a' b')))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    _ -> do 
      (tell . pure) (bk, TypeMismatch' (ExpectedType $ show $ expectedType env) (ActualType . show $ "A tuple type."))
      pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)


typeCheckPrefixPrec :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage PrefixPrec -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckPrefixPrec (PUMinus bk e) = do 
  env <- ask
  MkSomeExpression @e' e' <- withExpectedType (Just $ Z) $ fst <$> typeCheckExpr e
  case (sing @e',expectedType env) of 
    (STCon (matches @"Z" -> Just Refl) SNil, et) | et == Just (Z) || et == Nothing 
      -> pure (MkSomeExpression $ Minus (Val 0) e', Z)
    _ -> do 
      (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ Z) (ActualType . show $ demote @e'))
      pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

typeCheckPrefixPrec (OfHigherPrefixPrec e) = typeCheckExpr e


typeCheckPostfixPrec :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage PostfixPrec -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckPostfixPrec (PApp bk _ []) = do 
  (tell . pure) (bk, NonImplementedFeature "Functions with no arguments")
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckPostfixPrec (PApp bk (yieldVarName -> Just "fst") [arg]) = do 
  env <- ask 
  MkSomeExpression @arg' arg' <- withExpectedType Nothing $ fst <$> typeCheckExpr arg 
  case sing @arg' of 
    STCon (matches @"Tuple" -> Just Refl) (SCons @_ @sa sa (SCons sb SNil)) -> withSingI sa $ withSingI sb $ case expectedType env of
      Nothing ->  pure (MkSomeExpression $ FstT arg', demote @sa) 
      Just et -> case toSing et of 
        SomeSing @_ @st st 
          ->  withSingI st 
          $ case upcastable @st @sa of 
            SameTypeUB _ -> pure (MkSomeExpression $ FstT arg', demote @sa) 
            LeftUB _ 
              -> eqWeakening @(UpperBound st sa) @(Just st)
              $ pure (MkSomeExpression $ Subtyped @st $ FstT arg', et)
            _ -> do
              (tell . pure) (bk, TypeMismatch' (ExpectedType $ show et) (ActualType . show $ demote @sa))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    _ -> do 
      (tell . pure) (bk, TypeMismatch' (ExpectedType "A tuple argument") (ActualType . show $ demote @arg'))
      pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckPostfixPrec (PApp bk (yieldVarName -> Just "snd") [arg]) = do 
  env <- ask 
  MkSomeExpression @arg' arg' <- withExpectedType Nothing $ fst <$> typeCheckExpr arg 
  case sing @arg' of 
    STCon (matches @"Tuple" -> Just Refl) (SCons sa (SCons @_ @sb sb SNil)) -> withSingI sa $ withSingI sb $ case expectedType env of
      Nothing ->  pure (MkSomeExpression $ SndT arg', demote @sb) 
      Just et -> case toSing et of 
        SomeSing @_ @st st 
          ->  withSingI st 
          $ case upcastable @st @sb of 
            SameTypeUB _ -> pure (MkSomeExpression $ SndT arg', demote @sb) 
            LeftUB _ 
              -> eqWeakening @(UpperBound st sb) @(Just st)
              $ pure (MkSomeExpression $ Subtyped @st $ SndT arg', et)
            _ -> do
              (tell . pure) (bk, TypeMismatch' (ExpectedType $ show et) (ActualType . show $ demote @sb))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    _ -> do 
      (tell . pure) (bk, TypeMismatch' (ExpectedType "A tuple argument") (ActualType . show $ demote @arg'))
      pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

typeCheckPostfixPrec (PApp bk (yieldVarName -> Just "formula") [arg]) = do 
  env <- ask 
  MkSomeExpression arg' <- withExpectedType Nothing $ fst <$> typeCheckExpr arg 
  case arg' of 
    Var @ltype l -> case expectedType env of 
      Nothing ->  pure (MkSomeExpression $ Formula l, demote @ltype)

      Just et -> case toSing et of 
        SomeSing @_ @st st 
          -> withSingI st 
          $ case upcastable @st @ltype of 
            SameTypeUB _ -> pure (MkSomeExpression $ Formula l, demote @ltype)
            LeftUB _  
              -> eqWeakening  @(UpperBound st ltype) @(Just st)
              $ pure (MkSomeExpression $ Subtyped @st $ Formula l, et)
            _ -> do 
              (tell . pure) (bk, TypeMismatch' (ExpectedType $ show et) (ActualType . show $ demote @ltype))
              pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    _ -> do 
      (tell . pure) (bk, NonImplementedFeature "Formula Generalization")
      pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

          
typeCheckPostfixPrec (PApp bk f [arg]) = do 
  env <- ask 
  MkSomeExpression @f' f'     <- withExpectedType Nothing $ fst <$> typeCheckExpr f 
  MkSomeExpression @arg' arg' <- withExpectedType Nothing $ fst <$> typeCheckExpr arg 
  case sing @f' of 
    STCon (matches @"->" -> Just Refl) (SCons @_ @ltype ltype (SCons @_ @freturn freturn SNil))
      -> withSingI ltype 
      $ withSingI freturn
      $ withSingIFtype @arg' 
      $ case upcastable @ltype @arg' of 
        SameTypeUB _ 
          -> pure (MkSomeExpression $ App f' arg', demote @freturn)
        LeftUB _ 
          -> eqWeakening @(UpperBound ltype arg') @(Just ltype)
          $ pure (MkSomeExpression $ App f' (Subtyped @ltype @arg' arg'), demote @freturn)
        _ -> do 
          (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ demote @ltype) (ActualType . show $ demote @arg'))
          pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
    _ -> case expectedType env of 
      Just et -> do 
        (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ et) (ActualType . show $ demote @f'))
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
      Nothing -> do 
        (tell . pure) (bk, TypeMismatch' (ExpectedType $ "Function Type") (ActualType . show $ demote @f'))
        pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckPostfixPrec (PApp bk f (x:xs)) = typeCheckExpr (PApp bk (PApp bk f [x]) xs)
typeCheckPostfixPrec (PAppArr bk _ _) = do 
  (tell . pure) (bk, NonImplementedFeature "Arrays")
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckPostfixPrec (OfHigherPostfixPrec e) = typeCheckExpr e


typeCheckP8:: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage 8 -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckP8 (PPower bk _ _) = do  
  (tell . pure) (bk, NonImplementedFeature "Power notation" )
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP8 (OfHigher8 e) = typeCheckExpr e

typeCheckP7:: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage 7 -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckP7 (PMul bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just Z})(typeCheckP7 $ PMul bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil) 
        -> pure (MkSomeExpression $ Var @(PZ --> PZ --> PZ) "mul" $$ l' $$ r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP7 (PDiv bk _ _) = do  
  (tell . pure) (bk, NonImplementedFeature "Division notation" )
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP7 (PMod bk _ _) = do  
  (tell . pure) (bk, NonImplementedFeature "Modulo notation" )
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP7 (OfHigher7 e) = typeCheckExpr e

typeCheckP6:: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage 6 -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckP6 (PPlus bk l r) = typeCheckExpr (PMinus bk l $ PParen bk $ PMinus bk (OfHigher6 $ PInt bk 0) r)
typeCheckP6 (PMinus bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP6 $ PMinus bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil) 
         -> pure (MkSomeExpression $ Minus l' r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP6 (OfHigher6 e) = typeCheckExpr e


typeCheckP4 :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage 4 -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckP4 (PLT bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP4 $ PLT bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil) 
        -> pure (MkSomeExpression $ Less l' r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP4 (PLTEQ bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP4 $ PLTEQ bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil) 
        -> pure (MkSomeExpression $ Var @(PZ --> PZ --> PZ) "lteq" $$ l' $$ r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP4 (PGT bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP4 $ PGT bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil)  
        -> pure (MkSomeExpression $ Var @(PZ --> PZ --> PZ) "gt" $$ l' $$ r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP4 (PGTEQ bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP4 $ PGTEQ bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil)  
        -> pure (MkSomeExpression $ Var @(PZ --> PZ --> PZ) "gteq" $$ l' $$ r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP4 (PEQ bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP4 $ PEQ bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil) 
        -> pure (MkSomeExpression $ Var @(PZ --> PZ --> PZ) "eq" $$ l' $$ r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP4 (PNEQ bk l r) = ask >>= \env -> case expectedType env of 
  Nothing -> local (\env' -> env'{expectedType=Just (Z)})(typeCheckP4 $ PNEQ bk l r)
  Just (Z) -> do 
    MkSomeExpression @l' l' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr l)
    MkSomeExpression @r' r' <- fst <$> local (\env' -> env'{expectedType=Just (Z)}) (typeCheckExpr r) 
    case (sing @l',sing @r') of 
      (STCon (matches @"Z" -> Just Refl) SNil, STCon (matches @"Z" -> Just Refl) SNil) 
        -> pure (MkSomeExpression $ Var @(PZ --> PZ --> PZ) "neq" $$ l' $$ r', Z )
      _ -> pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
  Just t -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ t ) (ActualType . show $ Z))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP4 (OfHigher4 e) = typeCheckExpr e


typeCheckP1 :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage 1 -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckP1 (PLambda bk [] _ _) = do
  (tell . pure) (bk, NonImplementedFeature "Functions with no arguments")
  pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP1 (PLambda bk [(yieldVarName -> Just arg, gltype)] mgbody body) = ask >>= \env -> case expectedType env of 
  Just et@(eltype0 :-> ebody0) -> case (toSing eltype0, toSing ebody0, toSing gltype) of
    ( SomeSing @_ @eltype eltype , SomeSing @_ @ebody ebody, SomeSing @_ @gltype' gltype') 
      -> withSingI eltype 
      $ withSingI ebody 
      $ withSingI gltype' 
      $ do 
        MkSomeExpression @body' body'
          <- withDeclaredFreshVar arg gltype 
          $ withExpectedType ( mgbody  <|> Just ebody0)
          $ fst <$> typeCheckExpr body 
        case (downcastable @eltype @gltype', upcastable @ebody @body' ) of 
          (SameTypeLB _, SameTypeUB _) -> pure (MkSomeExpression $ Lambda (mkVar @gltype' arg) body', et)
          (SameTypeLB _, LeftUB _) 
            -> eqWeakening @(UpperBound (eltype --> ebody) (gltype' --> body')) @(Just (eltype --> ebody)) 
            $ pure (MkSomeExpression $ Subtyped @(eltype --> ebody) $ Lambda (mkVar @gltype' arg) body', et)
          (LeftLB _, LeftUB _) 
            -> eqWeakening @(UpperBound (eltype --> ebody) (gltype' --> body')) @(Just (eltype --> ebody))
            $ pure (MkSomeExpression $ Subtyped @(eltype --> ebody) $ Lambda (mkVar @gltype' arg) body', et)
          (LeftLB _, SameTypeUB _) 
            -> eqWeakening @(UpperBound (eltype --> ebody) (gltype' --> body')) @(Just (eltype --> ebody))
            $ pure (MkSomeExpression $ Subtyped @(eltype --> ebody) $ Lambda (mkVar @gltype' arg) body', et)

          _ -> do 
            (tell . pure) (bk, TypeMismatch' (ExpectedType . show $ et ) (ActualType . show $ gltype :-> demote @body'))
            pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)

  Nothing ->  do
    MkSomeExpression @body' body'
      <- withDeclaredFreshVar arg gltype 
      $ withExpectedType ( mgbody )
      $ fst <$> typeCheckExpr body 
    case toSing gltype of 
      SomeSing @_ @gltype' gltype' 
        -> withSingI gltype' 
        $ pure (MkSomeExpression $ Lambda (mkVar @gltype' arg) body', gltype :-> demote @body')

  et -> do 
    (tell . pure) (bk, TypeMismatch' (ExpectedType $ show et) (ActualType "A function type"))
    pure (MkSomeExpression (Bottom (CustomError "") [] ), Top)
typeCheckP1 (PLambda bk (arg:args) mgbody body) 
  = typeCheckP1 $ PLambda bk [arg] Nothing  (PLambda bk args mgbody body) 
typeCheckP1 (OfHigher1 e) = typeCheckExpr e 

typeCheckP0 :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => EPrec ParsingStage 0 -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (SomeExpression m,Types) 
typeCheckP0 (OfHigher0 e) = typeCheckExpr e

-----------------------------
-- TypeCheck Actions 
-----------------------------


typeCheckA0 :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => ZP.A0 ParsingStage -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) (A m, TypeCheckEnv m)
typeCheckA0 (ZP.Print e _) = withExpectedType Nothing $ fst <$> typeCheckExpr e >>= \case 
  MkSomeExpression e' -> ask >>= \env -> pure (Print e',env)
typeCheckA0 (ZP.Decl tt (yieldVarName  -> Just x) e bk) = ask >>= \env ->
  withExpectedType Nothing $ case toSing tt of 
    SomeSing @_ @t' t' 
      -> withSingI t' 
      $ withExpectedType (Just tt) 
      $ withDeclaredVar (ABottom,env) bk x tt
      $ runAndReturnEnv  
      $ fst <$> typeCheckExpr e >>= \case 
        MkSomeExpression @e' e' -> case upcastable @t' @e' of 
          SameTypeUB _ ->  pure $ Assign (mkVar @t' x) e'
          LeftUB _ 
            -> eqWeakening @(UpperBound t' e') @(Just t')
            $ pure . Assign (mkVar @t' x) $ Subtyped @t' e'
          _ -> do 
            (tell . pure) (bk, TypeMismatch' (ExpectedType $ show tt) (ActualType . show $ demote @e'))
            pure ABottom 
typeCheckA0 (ZP.Assign (yieldVarName -> Just x) e bk) = withExpectedType Nothing $ ask >>= \env -> case M.lookup x $ getGamma env of 
  Nothing -> runAndReturnEnv $ do 
    (tell . pure) (bk, FromGammaError' $ VariableNotDefined x)
    pure ABottom 
  Just tt -> case toSing tt of 
    SomeSing @_ @t' t' 
      -> withSingI t' 
      $ withExpectedType (Just tt) 
      $ runAndReturnEnv  
      $ fst <$> typeCheckExpr e >>= \case 
        MkSomeExpression @e' e' ->  case upcastable @t' @e' of 
          SameTypeUB _ -> pure $ Reassign (mkVar @t' x) e'
          LeftUB _ 
            -> eqWeakening @(UpperBound t' e') @(Just t')
            $ pure . Reassign (mkVar @t' x) $ Subtyped @t' e'
          _ -> do 
            (tell . pure) (bk, TypeMismatch' (ExpectedType $ show tt) (ActualType . show $ demote @e'))
            pure ABottom 
typeCheckA0 (ZP.SysCommand "reset" _) = runAndReturnEnv . pure $ SysCommand "reset"
typeCheckA0 (ZP.SysCommand s bk) = runAndReturnEnv $ do 
  (tell . pure) (bk, NonImplementedFeature  $ "sys command: " <> show s <> ".")
  pure ABottom
typeCheckA0 (ZP.Decl _ _ _ bk) =  runAndReturnEnv $ do 
  (tell . pure) (bk, NonImplementedFeature  "Non string LValues.")
  pure ABottom
typeCheckA0 (ZP.Assign _ _ bk) = runAndReturnEnv $ do 
  (tell . pure) (bk, NonImplementedFeature  "Non string LValues.")
  pure ABottom


typeCheckA1 :: 
  ( Effects m
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  ) 
  => ZP.A1 ParsingStage -> ReaderT (TypeCheckEnv m) (WriterT (w (BookeepInfo,TypeCheckError))  m) ([A m], TypeCheckEnv m)
typeCheckA1 (ZP.OfA0 a) = (\(a',env) -> ([a'],env)) <$> typeCheckA0 a
typeCheckA1 (ZP.Seq _ a as) = fst <$> typeCheckA0 a >>= \case 
  a'@(Assign @ltype x e)
    -> withVar (varNameM x) (demote @ltype) (MkSomeExpression e)
    $ case as of 
      [] -> runAndReturnEnv $ pure [a']
      (a'':as') -> (\(xs,env) -> (a' :xs,env)) <$> typeCheckA1 (ZP.MkSeq a'' as')
  a'@(Reassign @ltype x e)
    -> withVar (varNameM x) (demote @ltype) (MkSomeExpression e)
    $ case as of 
      [] -> runAndReturnEnv $ pure [a']
      (a'':as') -> (\(xs,env) -> (a' :xs,env)) <$> typeCheckA1 (ZP.MkSeq a'' as')
  a'@(Print {}) -> case as of 
    [] -> runAndReturnEnv $ pure [a']
    (a'':as') -> (\(xs,env) -> (a' :xs,env)) <$> typeCheckA1 (ZP.MkSeq a'' as')
  a'@(SysCommand {}) -> case as of 
    [] -> runAndReturnEnv $ pure [a']
    (a'':as') -> (\(xs,env) -> (a' :xs,env)) <$> typeCheckA1 (ZP.MkSeq a'' as')
  a'@(ABottom) -> case as of 
    [] -> runAndReturnEnv $ pure [a']
    (a'':as') -> (\(xs,env) -> (a' :xs,env)) <$> typeCheckA1 (ZP.MkSeq a'' as')


-----------------------------
-- Aux Functions 
-----------------------------

runAndReturnEnv :: Monad m => ReaderT env m a -> ReaderT env m (a,env)
runAndReturnEnv ma = ask >>= \env -> (,env) <$> ma 


withDeclaredFreshVar :: Monad m 
  => String -> Types -> ReaderT (TypeCheckEnv f) m a -> ReaderT (TypeCheckEnv f) m a
withDeclaredFreshVar x t = local (\env -> env{getGamma = M.insert x t $ getGamma env}) 

withDeclaredVar :: 
  ( Monad m 
  , Monoid (w (BookeepInfo,TypeCheckError))
  , Applicative w
  )
  => a 
  -> BookeepInfo 
  -> String 
  -> Types 
  -> ReaderT (TypeCheckEnv f) (WriterT (w (BookeepInfo,TypeCheckError)) m) a 
  -> ReaderT (TypeCheckEnv f) (WriterT (w (BookeepInfo,TypeCheckError)) m) a
withDeclaredVar def bk x t ma = do
  env <- getGamma <$> ask 
  a <- local (\env -> env{getGamma = M.insert x t $ getGamma env}) ma
  case not $ M.member  x  env  of 
    True -> pure a 
    False -> do 
      (tell . pure) (bk, CustomError' $ "Variable re-declaration: " <> x) 
      pure def



withVar :: Monad m => String -> Types -> SomeExpression f -> ReaderT (TypeCheckEnv f) m a -> ReaderT (TypeCheckEnv f) m a
withVar x t e fa
  = withDeclaredFreshVar x t 
  $ local (\env -> env{getCValues = M.insert x e $ getCValues env}) 
  $ fa


withExpectedType :: Monad m => Maybe Types -> ReaderT (TypeCheckEnv f) m a -> ReaderT (TypeCheckEnv f) m a
withExpectedType t = local (\env-> env{expectedType=t})


