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
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}


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
import Data.Foldable (traverse_, for_, foldrM, foldlM)
import Data.List qualified as List
import Zilly.Puzzle.Action.Exports (HasTypeEnv(..))
import Control.Monad (unless, zipWithM)
import Data.Traversable (for)
import Debug.Trace (trace)
import Control.Concurrent.MVar (MVar, tryTakeMVar, putMVar)
import Control.Monad.IO.Class
import Data.Functor (void)

data TCTag
type PTInfo = (MVar T.Types, BookeepInfo)

$(genCtxInstances ''TCTag ''PTInfo)

data Scheme = Forall (S.Set T.TVar) T.Types

setType :: MonadIO m => PTInfo -> T.Types -> m PTInfo
setType (mvar,bk) t = liftIO $ tryTakeMVar mvar >> putMVar mvar t >> pure (mvar,bk)

setType' :: MonadIO m => PTInfo -> m T.Types -> m T.Types
setType' pt mt = do
  t <- mt
  void $ setType pt t
  pure t

data Constraint
  = EqConstraint T.Types T.Types
  | TcConstraint T.Name T.Types [T.Types]

pattern EqTcConstraint :: T.Types -> Constraint
pattern EqTcConstraint t = TcConstraint "Eq" t []

pattern NumTcConstraint :: T.Types -> Constraint
pattern NumTcConstraint t = TcConstraint "Num" t []

pattern IsBooleanTcConstraint :: T.Types -> Constraint
pattern IsBooleanTcConstraint t = TcConstraint "IsBoolean" t []

pattern CoerceTcConstraint :: T.Types -> T.Types -> Constraint
pattern CoerceTcConstraint a b = TcConstraint "Coerce" a [b]

pattern UpperBoundConstraint :: T.Types -> T.Types -> T.Types -> Constraint
pattern UpperBoundConstraint a b c = TcConstraint "UpperBound" a [b,c]

pattern HasFieldConstraint :: T.Types -> Text.Text -> T.Types -> Constraint
pattern HasFieldConstraint a field b <- TcConstraint "HasField" a [T.StringDataKind field, b]
  where HasFieldConstraint a field b  = TcConstraint "HasField" a [T.StringDataKind (fromString $ show field), b]

pattern ImplementsFormulaConstraint :: T.Types -> Constraint
pattern ImplementsFormulaConstraint a = TcConstraint "ImplementsFormula" a []

pattern ImplementsRandomConstraint :: T.Types -> Constraint
pattern ImplementsRandomConstraint a = TcConstraint "ImplementsRandom" a []

pattern ImplementsPowerConstraint :: T.Types -> T.Types -> T.Types -> Constraint
pattern ImplementsPowerConstraint a b c = TcConstraint "ImplementsPower" a [b,c]

pattern LowerBoundConstraint :: T.Types -> T.Types -> T.Types -> Constraint
pattern LowerBoundConstraint a b c = TcConstraint "LowerBound" a [b,c]

pattern BOrZTcConstraint :: T.Types -> Constraint
pattern BOrZTcConstraint t = TcConstraint "BOrZ" t []






instance Show Constraint where
  show (EqConstraint a b) = show a <> " ~ " <> show b
  show (TcConstraint name t args) =
    Text.unpack name <> " " <> show t <> " " <> unwords (show <$> args)

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

class (MonadIO m, HasTypeEnv m) => InferMonad m where
  fresh :: m T.Types
  constraint :: Constraint -> m ()
  gamma :: m Gamma
  getConstraints :: m [Constraint]
  reportTCError :: String -> m ()
  throwIrrecoverableError :: String -> m a
  withVar :: String -> Scheme -> m a -> m a

withVars :: (Foldable f, InferMonad m)
 => f (String, Scheme) -> m a -> m a
withVars vars a = foldr (\(n,s) acc -> withVar n s acc) a vars

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set T.TVar

instance Substitutable  T.Types where
  ftv (T.TVar v) =  S.singleton v
  ftv (T.TCon _ ts) = S.unions $ ftv <$> ts
  -- type families should not bound type variables
  ftv (T.TFamApp _ t ts) = S.unions $ ftv t : (ftv <$> ts)
  ftv (T.TConstraint _ t args ret)
    = S.unions $ ftv t : (ftv <$> args) <> [ftv ret]
  ftv (T.RTVar {}) = S.empty

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
  apply _ tfapp@(T.TFamApp {}) = error "Cannot apply substitution to type family application"
  apply s (T.TConstraint name t args ret)
    = T.TConstraint name (apply s t) (apply s <$> args) (apply s ret)
  apply s (T.RTVar n) = applySubst s n

instance Substitutable Scheme where
  ftv (Forall vars t) = S.difference (ftv t) vars
  apply s (Forall vars t) = Forall vars (apply (filterSubst (`S.notMember` vars) s) t)

instance Substitutable Constraint where
  ftv (EqConstraint a b) = S.union (ftv a) (ftv b)
  ftv (TcConstraint _ a as) = S.unions (ftv a : fmap ftv as)
  apply s (EqConstraint a b) = EqConstraint (apply s a) (apply s b)
  apply s (TcConstraint name a as) = TcConstraint name (apply s a) (fmap (apply s) as)

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
  infer :: (InferMonad m) => a -> m T.Types



instance Inferable (A0 TCTag) where
  infer (Print e _) = infer e
  infer (Decl T.ZInfer (yieldVarName -> Just v) e ctx) = do
    tx <- fresh
    te <- withVar v (Forall S.empty tx) $ infer e
    void $ setType ctx te
    pure te
  infer (Decl t (yieldVarName -> Just v) e ctx) = do
    gammaCtx <- gamma
    let es = generalize gammaCtx t
    te <- withVar v es $ infer e
    void $ setType ctx te
    pure te
  infer a = throwIrrecoverableError
    $ "Action "
    <> show a
    <> " should not be inferable."


instance SingI n => Inferable (EPrec TCTag n) where
  infer e | Just Refl <- matches @Atom (sing @n) = case e of
    PInt   ctx _  -> setType' ctx $ pure T.Z
    PFloat ctx _  -> setType' ctx $ pure T.ZDouble
    PBool  ctx _  -> setType' ctx $ pure T.ZBool
    PString ctx _ -> setType' ctx $ pure T.ZString
    PVar ctx v  -> setType' ctx $ do
      gammaEnv <- gamma
      case M.lookup (fromString v) gammaEnv of
        Just sigma -> instantiate sigma
        Nothing    -> do
          reportTCError $ "Unbound variable: " <> v
          fresh
    PTuple ctx a b xs -> setType' ctx
      $ T.NTuple <$> infer a <*> infer b <*> traverse infer xs
    PParen ctx a -> setType' ctx $ infer a
    PArray ctx as -> setType' ctx $ traverse infer as >>= \case
      [] -> do
        natKind <- fresh
        t <- fresh
        pure $ T.TCon "array" [natKind, t]
      (x:xs) -> case foldl (\acc t -> acc >>= T.upperBound t) (Just x) xs of
        Just ub -> do
          traverse_ (\t -> constraint $ UpperBoundConstraint t ub ub) (x:xs)
          natKind <- fresh
          pure $ T.TCon "array" [natKind, ub]
        Nothing -> do
          reportTCError
            $ "Could not find common supertype for array elements: "
            <> List.intercalate ", " ((\(a,t) -> show a <> " : " <> show t) <$> (as `zip` (x:xs)) )
          natKind <- fresh
          ub <- fresh
          pure $ T.TCon "array" [natKind, ub]
    PDefer ctx a -> setType' ctx $ T.Lazy <$> infer a
    PIf ctx (c,l,r) -> setType' ctx $ do
      {-
       - we need typeclasses for a nice If, since the condition wants a boolean or an int.
       - so the type of if would be:
       -
       -  if :: (IsBoolean c) => c -> a -> a -> a

       oh crap, we also need to support subtyping, so the type of if would be:

        if :: (IsBoolean c, Coerce a ub, Coerce b ub) => c -> a -> b -> ub
      -}
      tc <- infer c
      constraint $ IsBooleanTcConstraint tc
      tL <- infer l
      tR <- infer r
      tub <- upperBoundM tL tR
      let cs = S.fromList
            [ ("IsBoolean", tc, [])
            , ("Coerce", tL, [tub])
            , ("Coerce", tR, [tub])
            ]
      -- constraint $ CoerceTcConstraint tL tub
      -- constraint $ CoerceTcConstraint tR tub
      pure $ T.TConstraints cs tub

    PMatch mctx e branches -> setType' mctx $ do
      tE <- infer e
      ts <- for branches $ \(p,b) -> do
        (tP,ctx) <- inferAndBind p
        constraint $ UpperBoundConstraint tP tE tE
        withVars (M.toList ctx) $ infer b
      case ts of
        [] -> T.Bot <$ reportTCError "Match expression has no branches"
        (t:ts') -> case foldr (\ta mtb -> mtb >>= T.upperBound ta) (Just t) ts' of
          Nothing -> do
            reportTCError
              $ "Could not find common supertype for match branches: "
              <> List.intercalate ", " ((\(a,t) -> show a <> " : " <> show t) <$> (branches `zip` ts))
            fresh
          Just ub -> do
            for_ ts' (\t -> constraint $ UpperBoundConstraint t ub ub)
            pure ub

    PECons ctx name es -> setType' ctx $ lookupCons name >>= \case
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
    PUMinus ctx a -> setType' ctx $ do
      {-
       - UMinus needs a typeclass to type porperly:
       -
       -  uminus :: (Num a) => a -> a
       -
      -}
      ta <- infer a
      constraint $ NumTcConstraint ta
      pure $ T.TConstraint "Num" ta [] ta

    PNegate ctx a -> setType' ctx $ do
      tA <- infer a
      constraint $ EqConstraint tA T.ZBool
      pure T.ZBool
    OfHigherPrefixPrec a -> infer a

  infer e | Just Refl <- matches @PostfixPrec (sing @n) = case e of
    PAppArr ctx xs ix -> setType' ctx $ do
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
    PDotApp ctx e field -> setType' ctx $ do
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
      constraint $ HasFieldConstraint tE (Text.pack field) a
      pure $ T.TConstraint "HasField" tE [T.StringDataKind (fromString $ show field)] a

    PApp ctx (yieldVarName -> Just "formula") [arg] -> setType' ctx $ do
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
    PApp ctx (yieldVarName -> Just "random") [arg] -> setType' ctx $ do
      {-
        we need typeclasses:

        random :: ImplementsRandom x => x -> x-

        wait, now that we have bounded parametric polymorphism
        we no longer need to have these special cases! right?
      -}
      error "TODO"

    PApp ctx f [arg] -> setType' ctx $ do
      tf <- infer f
      ta <- infer arg
      x  <- fresh
      tb <- fresh
      constraint $ UpperBoundConstraint ta x x
      constraint $ EqConstraint tf (x T.:-> tb)
      let cs = S.fromList
            [ ("UpperBound", ta, [x,x])
            ]
      pure $ T.TConstraints cs  tb

    OfHigherPostfixPrec a -> infer a


    _ -> error "TODO"


  infer e | Just Refl <- matches @8 (sing @n) = case e of
    PPower ctx l r -> setType' ctx $ do
      tl <- infer l
      tr <- infer r
      a  <- fresh
      constraint $ ImplementsPowerConstraint tl tr a
      pure
        $ T.TConstraint "ImplementsPower" tl [tr,a]
        $  tl T.:-> tr T.:-> a

    OfHigher8 e -> infer e

  infer e | Just Refl <- matches @7 (sing @n) = case e of
    PMul ctx l r -> setType' ctx $ inferArith l r
    PDiv ctx l r -> setType' ctx $ inferArith l r
    PMod ctx l r -> setType' ctx $  do
      lt <- infer l
      rt <- infer r
      constraint $ EqConstraint lt T.Z
      constraint $ EqConstraint rt T.Z
      pure T.Z
    OfHigher7 e -> infer e

  infer e | Just Refl <- matches @6 (sing @n) = case e of
    PPlus ctx l r -> setType' ctx $ inferArith l r
    PMinus ctx l r -> setType' ctx $ inferArith l r
    PAppend ctx a b -> setType' ctx $ do
      ta <- infer a
      tb <- infer b
      constraint $ EqConstraint ta T.ZString
      constraint $ EqConstraint tb T.ZString
      pure T.ZString
    OfHigher6 e -> infer e

  infer e | Just Refl <- matches @4 (sing @n) = case e of
    PLT ctx l r   -> setType' ctx $ inferCmp l r
    PLTEQ ctx l r -> setType' ctx $ inferCmp l r
    PGT ctx l r   -> setType' ctx $ inferCmp l r
    PGTEQ ctx l r -> setType' ctx $ inferCmp l r
    PEQ ctx l r   -> setType' ctx $ inferEq l r
    PNEQ ctx l r  -> setType' ctx $ inferEq l r
    OfHigher4 e -> infer e

  infer e | Just Refl <- matches @3 (sing @n) = case e of
    PAnd ctx a b -> setType' ctx $ inferBoolOp a b
    POr ctx a b  -> setType' ctx $ inferBoolOp a b
    OfHigher3 e -> infer e

  infer e | Just Refl <- matches @1 (sing @n) = case e of
    PLambda ctx [(yieldVarName -> Just arg, argT)] mret body -> setType' ctx $ do
      pT <- fresh
      constraint $ EqConstraint pT $ T.rtype argT
      let lambdaCtx =  ftv argT
      -- let lambdaCtx = S.empty
      let ps = Forall lambdaCtx pT
      et <- withVar arg ps $ infer body
      case mret of
        Nothing -> pure $ argT T.:-> et
        Just retT -> constraint (EqConstraint et retT) >> pure (argT T.:-> retT)
    PLambda {} -> do
      throwIrrecoverableError "Illegal Lambda with multiple arguments in typechecking phase."
    OfHigher1 e -> infer e


  infer e | Just Refl <- matches @0 (sing @n) = case e of
    OfHigher0 e -> infer e



  infer e = throwIrrecoverableError
    $ "Expression "
    <> show e
    <> " could not be inferred."


instance Inferable (PIndexerExpression TCTag) where
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

class BindingInferable a where
  inferAndBind :: InferMonad m => a -> m (T.Types, Map String Scheme)

instance BindingInferable (PLPattern TCTag) where
  inferAndBind (PLVarPattern ctx v) = do
    t <- fresh
    let s = Forall S.empty t
    void $ setType ctx t
    pure (t, M.singleton v s)
  inferAndBind (PLWildcardPattern ctx) = do
    t <- fresh
    void $ setType ctx t
    pure (t, M.empty)
  inferAndBind (PLIntPattern ctx _) = setType ctx T.Z >> pure (T.Z, M.empty)
  inferAndBind (PLBoolPattern ctx _) = setType ctx T.ZBool >> pure (T.ZBool, M.empty)
  inferAndBind (PLStringPattern ctx _) = setType ctx T.ZString >> pure (T.ZString, M.empty)
  inferAndBind (PLFloatPattern ctx _) = setType ctx T.ZDouble >> pure (T.ZDouble, M.empty)
  inferAndBind (PLTuplePattern mctx p1 p2 ps) = do
    (t1,ctx1) <- inferAndBind p1
    (t2,ctx2) <- inferAndBind p2
    (ts,ctxs) <- unzip <$> traverse inferAndBind ps
    let ctx = M.unions (ctx1:ctx2:ctxs)
    let ft = T.NTuple t1 t2 ts
    void $ setType mctx ft
    pure (ft,ctx)
  inferAndBind (PLARecordPattern mctx fields) = do
    let ctx = M.fromList $ fmap (Forall S.empty) <$> fields
    let ft = T.ARecord $ fmap (\(x,t) -> (fromString x,t)) fields
    void $ setType mctx ft
    pure (ft, ctx)
  inferAndBind (PLConstructorPattern mctx name ps) = lookupCons name >>= \case
    Nothing -> do
      reportTCError $ "Unknown constructor in pattern: " <> name
      t <- fresh
      void $ setType mctx t
      pure (t, M.empty)
    Just (t,ts) -> do
      unless (length ts == length ps) $ reportTCError
        $ "Constructor " <> name <> " expects "
        <> show (length ts) <> " arguments, but got "
        <> show (length ps) <> " in pattern"
      ctxs <- for (ps `zip` ts) $ \(p,t') -> do
        (t'',ctx) <- inferAndBind p
        constraint $ EqConstraint t'' t'

        pure ctx
      let ctx = M.unions ctxs
      void $ setType mctx t
      pure (t, ctx)

instance Inferable (PLPattern TCTag) where
  infer = fmap fst . inferAndBind

instance BindingInferable (PPaternGuard TCTag) where
  inferAndBind (PExprGuard ctx e)
    = infer e
    >>= \t -> constraint (EqConstraint t T.ZBool)
    >> setType ctx t
    >> pure (t, M.empty)
  inferAndBind (PBindingGuard mctx lp e) = do
    tE <- infer e
    (tP, ctx) <- inferAndBind lp
    constraint $ EqConstraint tE tP
    void $ setType mctx tP
    pure (tP, ctx)

instance Inferable (PPaternGuard TCTag) where
  infer = fmap fst . inferAndBind

instance BindingInferable (PPattern TCTag) where
  inferAndBind (MkPPattern lp guards) = do
    (tP, ctx) <- inferAndBind lp
    ctxF <- (\f -> foldlM f ctx guards) $ \ctx' g -> do
      (tG, ctxG) <- inferAndBind g
      constraint $ EqConstraint tG tP
      pure (ctx' `M.union` ctxG)
    pure (tP, ctxF)

instance Inferable (PPattern TCTag) where
  infer = fmap fst . inferAndBind

unify :: InferMonad m => T.Types -> T.Types -> m Subst
unify a b | a == b = pure emptySubst
unify (T.TVar v) t = bind v t
unify t (T.TVar v) = bind v t
unify (T.TConstraints cs1 t1) (T.TConstraints cs2 t2)
  | (not . null) cs1 || (not . null) cs2 = do
    s1 <- unifyConstraints cs1 cs2
    s2 <- unify (apply s1 t1) (apply s1 t2)
    pure (s2 `composeSubst` s1)
unify a@(T.TCon n1 ts1) b@(T.TCon n2 ts2)
  | n1 == n2 && length ts1 == length ts2 = unifyMany ts1 ts2
  | otherwise = throwIrrecoverableError
      $ "Type mismatch: cannot unify " <> show a <> " with " <> show b
unify (T.RV {}) _ = pure emptySubst
unify _ (T.RV {}) = pure emptySubst
unify (T.TFamApp {}) _ = throwIrrecoverableError "User defined type families  are not supported"
unify _ (T.TFamApp {}) = throwIrrecoverableError "User defined type families are not supported"
unify a b = do
  reportTCError
    $ "Type mismatch: cannot unify " <> show a <> " with " <> show b
  pure emptySubst


unifyMany :: InferMonad m => [T.Types] -> [T.Types] -> m Subst
unifyMany [] [] = pure emptySubst
unifyMany (x:xs) (y:ys) = do
  s1 <- unify x y
  s2 <- unifyMany (apply s1 xs) (apply s1 ys)
  pure (s2 `composeSubst` s1)
unifyMany _ _ = throwIrrecoverableError "Unification mismatch: lists have different lengths"

unifyConstraints :: forall m. InferMonad m
  => Set (T.Name, T.Types, [T.Types])
  -> Set (T.Name, T.Types, [T.Types])
  -> m Subst
unifyConstraints cs1 cs2 = foldrM f emptySubst $ M.toList cs3m
  where
    cs1m = M.fromListWith (++) [ (c, t:ts) | (c,t,ts) <- S.toList cs1 ]
    cs2m = M.fromListWith (++) [ (c, t:ts) | (c,t,ts) <- S.toList cs2 ]
    cs3m = M.intersectionWith (,) cs1m cs2m

    f :: (T.Name, ([T.Types], [T.Types])) -> Subst -> m Subst
    f (_,(as,bs)) s = do
      s' <- unifyMany (apply s as) (apply s bs)
      pure (s' `composeSubst` s)


occurs :: T.TVar -> T.Types -> Bool
occurs v t = v `S.member` ftv t

bind :: InferMonad m => T.TVar -> T.Types -> m Subst
bind v@(T.TV v') t
  | v `occurs` t = throwIrrecoverableError
      $ "Occurs check failed: cannot construct infinite type: " <> Text.unpack v' <> " in " <> show t
  | otherwise    = pure $ singletonSubst v t

solve :: InferMonad m => Subst -> [Constraint] -> m Subst
solve s [] = trace "base case" pure s
solve s (EqConstraint t1 t2 : cs) = do
  s1 <- unify t1 t2
  solve (s1 `composeSubst` s) (apply s1 cs)
-- at this point we only care about substitutions
-- and constraints DO NOT generate substitutions
-- rather, we have to CHECK if the constraints are solvable
-- at a later step
solve s (TcConstraint {} : css) = do
  solve s css



upperBoundM :: InferMonad m => T.Types -> T.Types -> m T.Types
upperBoundM a b | a == b = pure a
upperBoundM (a T.:-> b) (c T.:-> d)
  = (T.:->) <$> lowerBoundM a c <*> upperBoundM b d
upperBoundM (T.NDArray n a) (T.NDArray m b)
  | n == m    = T.NDArray n <$> upperBoundM a b
  | otherwise = do
      reportTCError
        $ "Cannot compute upper bound of arrays with different ranks: "
        <> show n <> " and " <> show m
      fresh
upperBoundM (T.TCon "array" [n1,a]) (T.TCon "array" [n2,b]) = do
  constraint $ EqConstraint n1 n2
  -- T.TConstraint "~" n1 [n2] . T.TCon "array" . (n1 :) . pure <$> upperBoundM a b
  T.TCon "array" . (n1 :) . pure <$> upperBoundM a b

upperBoundM (T.Lazy a) (T.Lazy b) = T.Lazy <$> upperBoundM a b
upperBoundM T.Z T.F = pure T.F
upperBoundM T.F T.Z = pure T.F
upperBoundM (T.NTuple a b xs) (T.NTuple c d ys)
  | length xs == length ys
    = T.NTuple
    <$> upperBoundM a c
    <*> upperBoundM b d
    <*> zipWithM upperBoundM xs ys
  | otherwise = do
      reportTCError
        $ "Cannot compute upper bound of tuples with different lengths: "
        <> show (length xs) <> " and " <> show (length ys)
      fresh
upperBoundM T.Top _ = pure T.Top
upperBoundM _ T.Top = pure T.Top
upperBoundM T.Bot a = pure a
upperBoundM a T.Bot = pure a
upperBoundM (T.Lazy a) b = T.Lazy <$> upperBoundM a b
upperBoundM a (T.Lazy b) = T.Lazy <$> upperBoundM a b
upperBoundM T.ZInfer a = pure a
upperBoundM a T.ZInfer = pure a
upperBoundM (T.ARecord a) (T.ARecord b) = do
  let amap = M.fromList a
  let bmap = M.fromList b
  let keys = S.union (S.fromList (M.keys amap)) (S.fromList (M.keys bmap))
  fields <- for (S.toList keys) $ \k -> case (M.lookup k amap, M.lookup k bmap) of
    (Just t1, Just t2) -> do
      t <- upperBoundM t1 t2
      pure (k,t)
    (Just t1, Nothing) -> pure (k,t1)
    (Nothing, Just t2) -> pure (k,t2)
    (Nothing, Nothing) -> error "Impossible"
  pure $ T.ARecord fields
upperBoundM (T.TVar a) b = case b of
  T.TVar b' | a == b' -> pure b
  _                   -> do
    c <- fresh
    constraint $ UpperBoundConstraint (T.TVar a) b c
    pure $ T.TConstraint "UpperBound" (T.TVar a) [b, c] c
upperBoundM a (T.TVar b) = case a of
  T.TVar a' | a' == b -> pure a
  _                   -> do
    c <- fresh
    constraint $ UpperBoundConstraint a (T.TVar b) c
    pure $ T.TConstraint "UpperBound" a [T.TVar b, c] c
upperBoundM (T.TConstraints cs1 t1) (T.TConstraints cs2 t2) = do
  t <- upperBoundM t1 t2
  let cs = S.union cs1 cs2
  pure $ T.TConstraints cs t
upperBoundM (T.TConstraints cs t1) t2 = do
  t <- upperBoundM t1 t2
  pure $ T.TConstraints cs t
upperBoundM t1 (T.TConstraints cs t2) = do
  t <- upperBoundM t1 t2
  pure $ T.TConstraints cs t

upperBoundM (T.RV x) a = case T.rtype x of
  T.RV y -> do
    rvy <- fresh
    c   <- fresh
    constraint $ EqConstraint (T.RV y) rvy
    constraint $ UpperBoundConstraint rvy a c
    let cs = S.fromList
          [ ("UpperBound", rvy, [a, c])
          ]
    pure $ T.TConstraints cs c
  t -> upperBoundM t a
upperBoundM a (T.RV x) = case T.rtype x of
  T.RV y -> do
    rvy <- fresh
    c   <- fresh
    constraint $ EqConstraint (T.RV y) rvy
    constraint $ UpperBoundConstraint rvy a c
    let cs = S.fromList
          [ ("UpperBound", rvy, [a, c])
          ]
    pure $ T.TConstraints cs c
  t -> upperBoundM a t
upperBoundM a b = do
  reportTCError
    $ "Could not compute upper bound of types: "
    <> show a <> " and " <> show b
  fresh


lowerBoundM :: InferMonad m => T.Types -> T.Types -> m T.Types
lowerBoundM a b | a == b = pure a
lowerBoundM (a T.:-> b) (c T.:-> d)
  = (T.:->) <$> upperBoundM a c <*> lowerBoundM b d
lowerBoundM (T.NDArray n a) (T.NDArray m b)
  | n == m    = T.NDArray n <$> lowerBoundM a b
  | otherwise = do
      reportTCError
        $ "Cannot compute lower bound of arrays with different ranks: "
        <> show n <> " and " <> show m
      fresh
lowerBoundM (T.TCon "array" [n1,a]) (T.TCon "array" [n2,b]) = do
  constraint $ EqConstraint n1 n2
  -- T.TConstraint "~" n1 [n2] . T.TCon "array" . (n1 :) . pure <$> lowerBoundM a b
  T.TCon "array" . (n1 :) . pure <$> lowerBoundM a b
lowerBoundM (T.Lazy a) (T.Lazy b) = T.Lazy <$> lowerBoundM a b
lowerBoundM T.Z T.F = pure T.Z
lowerBoundM T.F T.Z = pure T.Z
lowerBoundM (T.NTuple a b xs) (T.NTuple c d ys)
  | length xs == length ys
    = T.NTuple
    <$> lowerBoundM a c
    <*> lowerBoundM b d
    <*> zipWithM lowerBoundM xs ys
  | otherwise = do
      reportTCError
        $ "Cannot compute lower bound of tuples with different lengths: "
        <> show (length xs) <> " and " <> show (length ys)
      fresh
lowerBoundM T.Top a = pure a
lowerBoundM a T.Top = pure a
lowerBoundM T.Bot _ = pure T.Bot
lowerBoundM _ T.Bot = pure T.Bot
lowerBoundM (T.Lazy a) b = lowerBoundM a b
lowerBoundM a (T.Lazy b) = lowerBoundM a b
lowerBoundM T.ZInfer a = pure a
lowerBoundM a T.ZInfer = pure a
lowerBoundM (T.ARecord a) (T.ARecord b) = do
  let amap = M.fromList a
  let bmap = M.fromList b
  let keys = S.intersection (S.fromList (M.keys amap)) (S.fromList (M.keys bmap))
  fields <- for (S.toList keys) $ \k -> case (M.lookup k amap, M.lookup k bmap) of
    (Just t1, Just t2) -> do
      t <- lowerBoundM t1 t2
      pure (k,t)
    (Just t1, Nothing) -> pure (k,t1)
    (Nothing, Just t2) -> pure (k,t2)
    (Nothing, Nothing) -> error "Impossible"
  pure $ T.ARecord fields
lowerBoundM (T.TVar a) b = case b of
  T.TVar b' | a == b' -> pure b
  _                   -> do
    c <- fresh
    constraint $ LowerBoundConstraint (T.TVar a) b c
    pure $ T.TConstraint "LowerBound" (T.TVar a) [b, c] c
lowerBoundM a (T.TVar b) = case a of
  T.TVar a' | a' == b -> pure a
  _                   -> do
    c <- fresh
    constraint $ LowerBoundConstraint a (T.TVar b) c
    pure $ T.TConstraint "LowerBound" a [T.TVar b, c] c
lowerBoundM (T.TConstraints cs1 t1) (T.TConstraints cs2 t2) = do
  t <- lowerBoundM t1 t2
  let cs = S.intersection cs1 cs2
  pure $ T.TConstraints cs t
lowerBoundM (T.TConstraints cs t1) t2 = do
  t <- lowerBoundM t1 t2
  pure $ T.TConstraints cs t
lowerBoundM t1 (T.TConstraints cs t2) = do
  t <- lowerBoundM t1 t2
  pure $ T.TConstraints cs t
lowerBoundM (T.RV x) a = case T.rtype x of
  T.RV y -> do
    rvy <- fresh
    c   <- fresh
    constraint $ EqConstraint (T.RV y) rvy
    constraint $ LowerBoundConstraint rvy a c
    let cs = S.fromList
          [ ("LowerBound", rvy, [a, c])
          ]
    pure $ T.TConstraints cs c
  t -> lowerBoundM t a
lowerBoundM a (T.RV x) = case T.rtype x of
  T.RV y -> do
    rvy <- fresh
    c   <- fresh
    constraint $ EqConstraint (T.RV y) rvy
    constraint $ LowerBoundConstraint rvy a c
    let cs = S.fromList
          [ ("LowerBound", rvy, [a, c])
          ]
    pure $ T.TConstraints cs c
  t -> lowerBoundM a t
lowerBoundM a b = do
  reportTCError
    $ "Could not compute lower bound of types: "
    <> show a <> " and " <> show b
  fresh

inferArith ::
  ( Inferable a
  , Inferable b
  , InferMonad m
  )
  => a -> b ->  m T.Types
inferArith l r = do
  tl <- infer l
  tr <- infer r
  a  <- fresh
  constraint $ NumTcConstraint a
  constraint $ UpperBoundConstraint tl tr a
  let cs = S.fromList
        [ ("Num", a, [])
        -- , ("UpperBound", tl, [tr,a])
        ]
  pure $ T.TConstraints cs a

inferCmp ::
  ( Inferable a
  , Inferable b
  , InferMonad m
  )
  => a -> b ->  m T.Types
inferCmp l r = do
  tl <- infer l
  tr <- infer r
  a  <- fresh
  r  <- fresh
  constraint $ TcConstraint "UpperBound" tl [tr,a]
  constraint $ BOrZTcConstraint r
  let cs = S.fromList
        [ ("UpperBound", tl, [tr,a])
        , ("BOrZ", r, [])
        ]
  pure $ T.TConstraints cs r

inferEq ::
  ( Inferable a
  , Inferable b
  , InferMonad m
  )
  => a -> b ->  m T.Types
inferEq l r = do
  tl <- infer l
  tr <- infer r
  a  <- fresh
  ret  <- fresh
  trace ("tl: " <> show tl <> ", tr: " <> show tr <> ", a: " <> show a) (pure ())
  constraint $ TcConstraint "UpperBound" tl [tr,a]
  constraint $ BOrZTcConstraint ret
  constraint $ EqTcConstraint a
  let cs = S.fromList
        [ ("UpperBound", tl, [tr,a])
        , ("Eq", a, [])
        , ("BOrZ", ret, [])
        ]
  pure $ T.TConstraints cs ret

inferBoolOp
  :: ( Inferable a
     , Inferable b
     , InferMonad m
     )
  => a -> b ->  m T.Types
inferBoolOp l r = do
  tl <- infer l
  tr <- infer r
  constraint $ EqConstraint tl T.ZBool
  constraint $ EqConstraint tr T.ZBool
  pure T.ZBool


data UpperBoundDict ctx = UpperBoundDict
  { leftCoercion  :: Expr ctx -> Expr ctx
  , rightCoercion :: Expr ctx -> Expr ctx
  }
