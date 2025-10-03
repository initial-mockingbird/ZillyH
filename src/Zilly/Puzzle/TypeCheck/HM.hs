{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}


module Zilly.Puzzle.TypeCheck.HM where

import Zilly.Puzzle.Parser
import Zilly.Puzzle.Types.Exports qualified as T
import Data.Matchers
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as Text
import Prelude.Singletons (SingI(..) )
import Data.Singletons.Decide (type (:~:)(..))
import Data.String (IsString(..))
import Data.Foldable (traverse_, for_)
import Data.List qualified as List
import Zilly.Puzzle.Action.Exports (HasTypeEnv(..))
import Control.Monad (unless)
import Data.Traversable (for)
import Debug.Trace (trace)

data Scheme = Forall (S.Set T.TVar) T.Types

data Constraint
  = EqConstraint T.Types T.Types
  | TcConstraint T.Name T.Types [T.Types]


instance Show Constraint where
  show (EqConstraint a b) = show a <> " ~ " <> show b
  show (TcConstraint name t args) =
    Text.unpack name <> " " <> unwords (show <$> args) <> " " <> show t

data Subst = Subst (Map T.TVar T.Types)

instance Show Subst where
  show (Subst s)
    = "{"
    <> List.intercalate ", " [ Text.unpack v <> " |-> " <> show t | (T.TV v,t) <- M.toList s ]
    <> "}"

applySubst :: Subst -> T.TVar -> T.Types
applySubst (Subst s) v = M.findWithDefault (T.TVar v) v s

filterSubst :: (T.TVar -> Bool) -> Subst -> Subst
filterSubst p (Subst s) = Subst $ M.filterWithKey (\k _ -> p k) s

emptySubst :: Subst
emptySubst = Subst M.empty

singletonSubst :: T.TVar -> T.Types -> Subst
singletonSubst v t = Subst (M.singleton v t)

composeSubst :: Subst -> Subst -> Subst
composeSubst (Subst a) (Subst b) =
  Subst $ M.map (apply (Subst a)) (b `M.union` a)

type Gamma = Map T.TVar Scheme

class (Monad m, HasTypeEnv m) => InferMonad m where
  fresh :: m T.Types
  constraint :: Constraint -> m ()
  gamma :: m Gamma
  getConstraints :: m [Constraint]
  reportTCError :: String -> m ()
  throwIrrecoverableError :: String -> m a
  withVar :: String -> Scheme -> m a -> m a

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set T.TVar

instance Substitutable  T.Types where
  ftv (T.TVar v) =  S.singleton v
  ftv (T.TCon _ ts) = S.unions $ ftv <$> ts
  -- type families should not bound type variables
  ftv (T.TFamApp _ t ts) = S.unions $ ftv t : (ftv <$> ts)

  apply s (T.TVar v) = applySubst s v
  apply s (T.TCon n ts) = T.TCon n (apply s <$> ts)
  -- We want to apply substitutions to `RV`` args
  -- so we can try to reduce this constraint
  apply s (T.RV t) = T.RV $ apply s t
  -- Lilly does not support user defined type families
  -- and we only have RV. So this should never trigger.
  -- If we allowed type families, we would need to
  -- seek the environment for a reduction rule
  -- just like we did for RV.
  apply _ (T.TFamApp {}) = error "Cannot apply substitution to type family application"

instance Substitutable Scheme where
  ftv (Forall vars t) = S.difference (ftv t) vars
  apply s (Forall vars t) = Forall vars (apply (filterSubst (`S.notMember` vars) s) t)

instance Substitutable Constraint where
  ftv (EqConstraint a b) = S.union (ftv a) (ftv b)
  apply s (EqConstraint a b) = EqConstraint (apply s a) (apply s b)

instance (Traversable f, Substitutable a) => Substitutable (f a) where
  ftv = foldr (S.union . ftv) S.empty
  apply s = fmap (apply s)

generalize :: Gamma -> T.Types -> Scheme
generalize gammaEnv t = Forall vars t
  where vars = S.difference (ftv t) (ftv gammaEnv)

instantiate :: InferMonad m => Scheme -> m T.Types
instantiate (Forall vars t) = do
  newVars <- mapM (const fresh) (S.toList vars)
  let s = Subst $ M.fromList $ zip (S.toList vars) newVars
  return $ apply s t

class Inferable a where
  infer :: InferMonad m => a -> m T.Types

instance SingI n => Inferable (EPrec ctx n) where
  infer e | Just Refl <- matches @Atom (sing @n) = case e of
    PInt {}    -> pure T.Z
    PFloat {} -> pure T.ZDouble
    PBool {}   -> pure T.ZBool
    PString {} -> pure T.ZString
    PVar _ v  -> do
      gammaEnv <- gamma
      case M.lookup (fromString v) gammaEnv of
        Just sigma -> instantiate sigma
        Nothing    -> do
          reportTCError $ "Unbound variable: " <> v
          fresh
    PTuple _ a b xs -> T.NTuple <$> infer a <*> infer b <*> traverse infer xs
    PParen _ a -> infer a
    PArray _ as -> traverse infer as >>= \case
      [] -> fresh
      (x:xs) -> case foldl (\acc t -> acc >>= T.upperBound t) (Just x) xs of
        Just ub -> do
          traverse_ (constraint . EqConstraint ub) (x:xs)
          natKind <- fresh
          pure $ T.TCon "array" [natKind, ub]
        Nothing -> do
          reportTCError
            $ "Could not find common supertype for array elements: "
            <> List.intercalate ", " ((\(a,t) -> show a <> " : " <> show t) <$> (as `zip` (x:xs)) )

          natKind <- fresh
          ub <- fresh
          pure $ T.TCon "array" [natKind, ub]
    PDefer _ a -> T.Lazy <$> infer a
    PIf _ (c,l,r) -> do
      {-
       - we need typeclasses for a nice If, since the condition wants a boolean or an int.
       - so the type of if would be:
       -
       -  if :: (IsBoolean c) => c -> a -> a -> a

       oh crap, we also need to support subtyping, so the type of if would be:

        if :: (IsBoolean c, Coerce a ub, Coerce b ub) => c -> a -> b -> ub
      -}
      tc <- infer c
      constraint $ TcConstraint "IsBoolean" tc []
      tL <- infer l
      tR <- infer r
      tub <- case T.upperBound tL tR of
        Just ub -> do
          constraint $ TcConstraint "Coerce" tL [ub]
          constraint $ TcConstraint "Coerce" tR [ub]
          pure ub
        Nothing -> do
          reportTCError
            $ "Could not find common supertype for if branches: "
            <> show tL <> " and " <> show tR
          fresh
      let cs = S.fromList
            [ ("IsBoolean", tc, [])
            , ("Coerce", tL, [tub])
            , ("Coerce", tR, [tub])
            ]
      pure $ T.TConstraints cs tub

    PMatch _ e branches -> do
      tE <- infer e
      ts <- for branches $ \(p,b) -> do
        tP <- infer p
        constraint $ EqConstraint tE tP
        infer b
      case ts of
        [] -> T.Bot <$ reportTCError "Match expression has no branches"
        (t:ts') -> case foldr (\ta mtb -> mtb >>= T.upperBound ta) (Just t) ts' of
          Nothing -> do
            reportTCError
              $ "Could not find common supertype for match branches: "
              <> List.intercalate ", " ((\(a,t) -> show a <> " : " <> show t) <$> (branches `zip` ts))
            fresh
          Just ub -> do
            for_ ts' (constraint . EqConstraint ub)
            pure ub

    PECons _ name es -> lookupCons name >>= \case
      Nothing -> do
        reportTCError $ "Unknown constructor: " <> name
        fresh
      Just (t,ts) -> do
        unless (length ts == length es) $ reportTCError
          $ "Constructor " <> name <> " expects "
          <> show (length ts) <> " arguments, but got "
          <> show (length es)
        for_ (es `zip` ts) $ \(e,t') -> do
          t'' <- infer e
          constraint $ EqConstraint t'' t'
        pure t
    PEARecord _ fields -> do
      let (ks,vs) = unzip fields
      vs' <- traverse infer vs
      pure . T.ARecord $ (fmap fromString ks `zip` vs')

  infer e | Just Refl <- matches @PrefixPrec (sing @n) = case e of
    PUMinus _ a -> do
      {-
       - UMinus needs a typeclass to type porperly:
       -
       -  uminus :: (Num a) => a -> a
       -
      -}
      ta <- infer a
      constraint $ TcConstraint "Num" ta []
      pure $ T.TConstraint "Num" ta [] ta

    PNegate _ a -> do
      tA <- infer a
      constraint $ EqConstraint tA T.ZBool
      pure T.ZBool
    OfHigherPrefixPrec a -> infer a

  infer e | Just Refl <- matches @PostfixPrec (sing @n) = case e of
    PAppArr _ xs ix -> do
      let iShape = length ix
      tF <- infer xs
      btXS <- fresh
      let etX = T.NDArray iShape btXS
      constraint $ EqConstraint tF etX
      tixs <- traverse infer ix
      let fShape = length [1 | T.Tuple {} <- tixs]
      let fT = case fShape of
            0 -> btXS
            _ -> T.NDArray fShape btXS
      pure fT
    PDotApp _ e field -> do
      {-
       - x.field needs typeclasses. If x type is a polytype then
       - how do we know if x.field is valid?
       - answer: we constraint x to have type:
       - x :: (HasField x field a) => x
       - for some fresh a.
       - It is important to note that we can do this since
       - field is a literal, and thus we can reify it at compile time.
       - if it were an arbitrary expression, we would need dependent types.
       -}
      tE <- infer e
      a <- fresh
      pure $ T.TConstraint "HasField" tE [T.StringDataKind (fromString field)] a

    PApp _ (yieldVarName -> Just "formula") [arg] -> do
      {-
       - freak me, formula can only work on monotypes. Polytypes do not
       - carry information regarding their l-type as of rn.
       -
       - we COULD allow polytypes if we did some magic:
       -
       - formulaX :: ImplementsFormula ltype => RV(ltype) -> ltype
       -
       - and essentially dispaatch a different formulaX for each variable
       -
       - I think that the above works for arrays and tuples too?
       -
       -
      -}
      error "TODO"
    PApp _ (yieldVarName -> Just "random") [arg] -> do
      {-
        we need typeclasses:

        random :: ImplementsRandom x => x -> x-

        wait, now that we have bounded parametric polymorphism
        we no longer need to have these special cases! right?
      -}
      error "TODO"

    PApp _ f [arg] -> do
      tf <- infer f
      ta <- infer arg
      tb <- fresh
      constraint $ EqConstraint tf (ta T.:-> tb)
      pure tb

    OfHigherPostfixPrec a -> infer a



    _ -> error "TODO"


  infer e | Just Refl <- matches @8 (sing @n) = case e of
    PPower _ l r -> do
      tl <- infer l
      tr <- infer r
      a  <- fresh
      constraint $ TcConstraint "ImplementsPower" tl [tr,a]
      pure
        $ T.TConstraint "ImplementsPower" tl [tr,a]
        $  tl T.:-> tr T.:-> a


    OfHigher8 e -> infer e

  infer e | Just Refl <- matches @7 (sing @n) = case e of
    PMul _ l r -> do
      tl <- infer l
      tr <- infer r
      a  <- fresh
      constraint $ TcConstraint "Num" tl []
      constraint $ TcConstraint "Num" tr []
      error "TODO"
    PDiv _ _ _ -> error "TODO"
    PMod _ _ _ -> error "TODO"
    OfHigher7 e -> infer e

  infer e | Just Refl <- matches @6 (sing @n) = case e of
    PPlus _ _ _ -> error "TODO"
    PMinus _ _ _ -> error "TODO"
    PAppend _ a b -> do
      ta <- infer a
      tb <- infer b
      constraint $ EqConstraint ta T.ZString
      constraint $ EqConstraint tb T.ZString
      pure T.ZString
    OfHigher6 e -> infer e

  infer e | Just Refl <- matches @4 (sing @n) = case e of
    PLT _ _ _ -> error "TODO"
    PLTEQ _ _ _ -> error "TODO"
    PGT _ _ _ -> error "TODO"
    PGTEQ _ _ _ -> error "TODO"
    PEQ _ a b -> error "TODO"
    PNEQ _ a b -> error "TODO"
    OfHigher4 e -> infer e

  infer e | Just Refl <- matches @3 (sing @n) = case e of
    PAnd _ a b -> do
      ta <- infer a
      tb <- infer b
      constraint $ EqConstraint ta T.ZBool
      constraint $ EqConstraint tb T.ZBool
      pure T.ZBool
    POr _ a b -> do
      ta <- infer a
      tb <- infer b
      constraint $ EqConstraint ta T.ZBool
      constraint $ EqConstraint tb T.ZBool
      pure T.ZBool
    OfHigher3 e -> infer e

  infer e | Just Refl <- matches @1 (sing @n) = case e of
    PLambda _ [(yieldVarName -> Just arg, argT)] mret body -> do
      pT <- fresh
      constraint $ EqConstraint pT argT
      let ps = Forall S.empty pT
      et <- withVar arg ps $ infer body
      case mret of
        Nothing -> pure et
        Just retT -> constraint (EqConstraint et retT) >> pure retT
    OfHigher1 e -> infer e

  infer e | Just Refl <- matches @0 (sing @n) = case e of
    OfHigher0 e -> infer e



  infer e = undefined

instance Inferable (PIndexerExpression ctx) where
  infer (PIndex e) = do
    tE <- infer e
    constraint $ EqConstraint tE T.Z
    pure T.Z
  infer (PRangeIndexer (e1,e2)) = do
    t1 <- infer e1
    t2 <- infer e2
    constraint $ EqConstraint t1 T.Z
    constraint $ EqConstraint t2 T.Z
    pure (T.Tuple T.Z T.Z)

instance Inferable (PLPattern ctx) where
  infer (PLVarPattern _ v) = fresh
  infer (PLWildcardPattern _) = fresh
  infer (PLIntPattern _ _) = pure T.Z
  infer (PLBoolPattern _ _) = pure T.ZBool
  infer (PLStringPattern _ _) = pure T.ZString
  infer (PLFloatPattern _ _) = pure T.ZDouble
  infer (PLTuplePattern _ p1 p2 ps) = T.NTuple <$> infer p1 <*> infer p2 <*> traverse infer ps
  infer (PLARecordPattern _ fields)
    = pure
    . T.ARecord
    . fmap (\(x,t) -> (fromString x,t))
    $ fields
  infer (PLConstructorPattern _ name ps) = lookupCons name >>= \case
    Nothing -> do
      reportTCError $ "Unknown constructor in pattern: " <> name
      fresh
    Just (t,ts) -> do
      unless (length ts == length ps) $ reportTCError
        $ "Constructor " <> name <> " expects "
        <> show (length ts) <> " arguments, but got "
        <> show (length ps) <> " in pattern"
      for_ (ps `zip` ts) $ \(p,t') -> do
        t'' <- infer p
        constraint $ EqConstraint t'' t'
      pure t

instance Inferable (PPaternGuard ctx) where
  infer (PExprGuard _ e) = infer e >>= \t -> constraint (EqConstraint t T.ZBool) >> pure t
  infer (PBindingGuard _ lp e) = do
    tE <- infer e
    tP <- infer lp
    constraint $ EqConstraint tE tP
    -- CHECK THIS
    pure tP

instance Inferable (PPattern ctx) where
  infer (MkPPattern lp guards) = do
    tP <- infer lp
    for_ guards infer
    pure tP

unify :: InferMonad m => T.Types -> T.Types -> m Subst
unify a b | a == b = pure emptySubst
unify (T.TVar v) t = bind v t
unify t (T.TVar v) = bind v t
unify a@(T.TCon n1 ts1) b@(T.TCon n2 ts2)
  | n1 == n2 && length ts1 == length ts2 = unifyMany ts1 ts2
  | otherwise = throwIrrecoverableError
      $ "Type mismatch: cannot unify " <> show a <> " with " <> show b
  where
    unifyMany [] [] = pure emptySubst
    unifyMany (x:xs) (y:ys) = do
      s1 <- unify x y
      s2 <- unifyMany (apply s1 xs) (apply s1 ys)
      pure (s2 `composeSubst` s1)


occurs :: T.TVar -> T.Types -> Bool
occurs v t = v `S.member` ftv t

bind :: InferMonad m => T.TVar -> T.Types -> m Subst
bind v@(T.TV v') t
  | v `occurs` t = throwIrrecoverableError
      $ "Occurs check failed: cannot construct infinite type: " <> Text.unpack v' <> " in " <> show t
  | otherwise    = pure $ singletonSubst v t

solve :: InferMonad m => Subst -> [Constraint] -> m Subst
solve s [] = pure s
solve s (EqConstraint t1 t2 : cs) = do
  s1 <- unify t1 t2
  solve (s1 `composeSubst` s) (apply s1 cs)
