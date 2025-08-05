{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

module Zilly.Puzzle.Effects.Block where

import Zilly.Puzzle.Parser
import Zilly.Puzzle.Effects.CC
import Data.Kind (Type)
import Data.Set qualified as S
import Data.Graph.Inductive
import Data.Map qualified as M
import Data.List qualified as L
import Data.Foldable (for_, foldlM)
import Control.Monad.Error.Class
import Data.Matchers
import Data.Singletons (SomeSing(..),SingI(..),sing,demote, withSingI, toSing)
import Data.Singletons.Decide
import Control.Monad.IO.Class
import Debug.Trace (trace)

type Block a = [a]

data AError a
  = Deceased a
  | NonStaticallyConstructive a
  | RuntimeError (String, a)


type BlockEffects m a env =
  ( MonadCC m
  , Monad m
  , AccAction m a
  , ReportBlock m a
  , GetDependencies a
  , GetVar a
  , IsStaticallyConstructive a
  , EnvOperations m env
  , MonadError String m
  , EnvElem env ~ a
  , MonadIO m
  )

class ReportBlock m a where
  reportError :: AError a -> m ()

class AccAction m a where
  queueAction :: a -> m ()
  getAcc :: m [a]

class MonadCC m => CCActions m  where
  getQ :: m Int
  putQ :: Int -> m ()

class GetDependencies a where
  getDependencies :: a -> S.Set String

class GetVar a where
  getVar :: a -> S.Set String

class EnvOperations m env where
  type EnvElem env :: Type
  declare :: EnvElem env -> m env
  getEnv  :: m env
  inScope :: m (S.Set String)
  withEnv :: env -> m a -> m a


class IsStaticallyConstructive a where
  isStaticallyConstructive :: a -> Bool


dependOn ::
  ( GetDependencies a
  , GetVar a
  )
  => a -> a -> Bool
dependOn a b =
  let deps = getDependencies a in
  let vars = getVar b in
  not $ S.null $ S.intersection deps vars

-- (Dependency graph, Deceased)
buildDependencyGraph :: forall a.
  ( GetDependencies a
  , GetVar a
  ) => S.Set String -> [a] -> (Gr () (),[a])
buildDependencyGraph s xs = (dependencyGraph,deceased)
  where

  inScope' :: S.Set String
  inScope' = S.unions $ s : fmap getVar xs


  numbered :: [(Int, a)]
  numbered = [0..] `zip` xs

  numberedVar :: M.Map String Int
  numberedVar = M.fromList
    $  [ (x, i) | (i, a) <- numbered, x <- S.toList (getVar a) ]

  numberedDependencies :: [( Int, S.Set String )]
  numberedDependencies = fmap getDependencies <$> numbered

  (healthy,deceased') = L.partition
    (S.null . (`S.difference` inScope' ) . snd)
    numberedDependencies

  deceased :: [a]
  deceased = (xs !!) . fst <$> deceased'

  numberedBlockDependencies :: [(Int, S.Set String)]
  numberedBlockDependencies = [ (i, hs `S.difference` s) | (i,hs) <- healthy]

  -- x := y + z => [(y,x), (z,x)]
  blockDependencies :: [(Int,Int)]
  blockDependencies = do
    (i,hs) <- numberedBlockDependencies
    s <- S.toList hs
    let pred = numberedVar M.! s
    pure (pred,i)

  dependencyGraph :: Gr () ()
  dependencyGraph = mkGraph
    [ (i, ()) | (i, _) <- numbered ]
    [ (i , j, ()) | (i, j) <- blockDependencies ]


-- (Ready to Process, Cyclic, Deceased)
orderAs :: forall a.
  ( GetDependencies a
  , GetVar a
  ) => S.Set String -> [a] -> ([[a]], [[a]], [a])
orderAs s xs = (readyToProcess, cyclic, deceased)
  where
  (dependencyGraph,deceased) = buildDependencyGraph s xs

  go :: [[Int]] -> Gr () () -> ([[Int]],[[Int]])
  go acc g =
    let canProcess = nodes . nfilter ((== 0)  . indeg g) $ g in
    let next = delNodes canProcess g in
    case null canProcess of
      True -> (acc, go' [] next)
      False -> go (acc <> [canProcess]) next

  go' :: [[Int]] -> Gr () () -> [[Int]]
  go' acc g =
    let minIndeg = minimum $ indeg g <$> nodes g in
    let current = nodes . nfilter ((== minIndeg)  . indeg g) $ g in
    let next = delNodes current g in
    case null current of
      True -> acc
      False -> go' (acc <> [current]) next

  (readyToProcessN, cyclicN) = go [] dependencyGraph
  readyToProcess :: [[a]]
  readyToProcess = fmap (xs !! ) <$> readyToProcessN

  cyclic :: [[a]]
  cyclic = fmap (xs !! ) <$> cyclicN

partitionStaticallyConstructive ::
  ( IsStaticallyConstructive a
  ) => [[a]] -> ([[a]], [[a]])
partitionStaticallyConstructive xs
  = L.unzip
  $ (L.partition isStaticallyConstructive)
  <$> xs

processPending :: forall m a env.
  ( BlockEffects m a env
  )
  => (a -> m (env, a)) -> m (env, Block a)
processPending evalA = do
  as  <- getAcc
  symbolsInScope <- inScope @m @env
  trace ("Symbols in scope: " <> show symbolsInScope) $ pure ()
  let (readyToProcess
        , cyclic
        , deceased
        ) = orderAs symbolsInScope as
  let ( staticallyConstructive
        , nonStaticallyConstructive
        ) = partitionStaticallyConstructive cyclic



  for_ deceased $ reportError . Deceased
  for_ deceased queueAction
  for_ nonStaticallyConstructive
    $ \ls -> for_ ls $ reportError . NonStaticallyConstructive


  (env0,processed,runtimeErrs) <- evalBlocks readyToProcess

  trace ("processed: " <> show  (getVar <$> processed)) $ pure ()
  for_ runtimeErrs queueAction
  for_ runtimeErrs $ \err -> reportError $ RuntimeError ("", err)


  let (statConsContinue, statConsDeceseased)
        = unzip
        $ L.partition (S.null . getDependencies)
        <$> staticallyConstructive
  for_ statConsDeceseased $ flip for_ queueAction
  (env1, staticallyConstructiveDeclared) <- withEnv env0
    $ transformStatConsBlocks statConsContinue
  (env2, statConsProcessed, statErrs) <- withEnv env1
    $ evalBlocks staticallyConstructiveDeclared
  for_ statErrs queueAction
  pure (env2, processed <> statConsProcessed)

  where
  evalBlocks :: [[a]] -> m (env, [a], [a])
  evalBlocks [] = getEnv >>= \env -> pure (env, [], [])
  evalBlocks (xs:xss) = do
    (env, xs', errs) <- evalProgram' evalA xs
    case errs of
      [] -> do
        (env', xss', errs') <- withEnv env (evalBlocks xss)
        pure (env', xs' <> xss', errs')
      _ -> pure (env, xs', errs <> concat xss)
  transformStaticallyConstructive :: [a] -> m (env, [a])
  transformStaticallyConstructive xs
    = getEnv
    >>= \env -> (\ a xs' f -> foldlM f a xs') (env,[]) xs
       $ \(env0,acc) a -> withEnv env0 $ do
        env1 <- declare a
        pure (env1, acc <> [a])

  transformStatConsBlocks :: [[a]] -> m (env, [[a]])
  transformStatConsBlocks xs
    = getEnv
    >>= \env -> (\a xs' f -> foldlM f a xs') (env,[]) xs
    $ \(env0, acc) as -> do
      (env1,n) <- withEnv env0 $ transformStaticallyConstructive as
      pure (env1, acc <> [n])

evalProgram' :: forall m a env.
  (BlockEffects m a env)
  => (a -> m (env,a)) -> [a] -> m (env, [a], [a])
evalProgram' _ [] = getEnv >>= \env -> pure (env, [], [])
evalProgram' evalA (x : xs) = declare @m @env x >>= \env -> withEnv env $
  tryError (evalA x) >>= \case
    Left err -> do
      reportError $ RuntimeError (err,x)
      let (errs',continue) = L.partition (`dependOn` x) xs
      (e,as,es) <- evalProgram' evalA continue
      pure (e,as,x: (errs' <> es))
    Right (env', x') -> do
      (env'',xs',errs) <- withEnv env' (evalProgram' evalA xs)
      pure (env'', x' : xs', errs)



instance SingI n => GetDependencies (EPrec ctx n) where
  getDependencies e
    | Just Refl <- matches @Atom (sing @n)
    = case e of
      PVar _ s -> S.singleton s
      PTuple _ a b xs -> S.unions
        [ getDependencies x | x <- (a : b : xs)]
      PParen _ a -> getDependencies a
      PDefer _ s -> getDependencies s
      PIf _ (a, b, c) -> S.unions
        [ getDependencies a
        , getDependencies b
        , getDependencies c
        ]

      PInt _ _ -> S.empty
      PFloat _ _ -> S.empty
      PBool _ _ -> S.empty
      PString _ _ -> S.empty
    | Just Refl <- matches @PrefixPrec (sing @n)
    = case e of
      PUMinus _ a -> getDependencies a
      OfHigherPrefixPrec a -> getDependencies a
    | Just Refl <- matches @PostfixPrec (sing @n)
    = case e of
      PApp _ f args -> S.unions
        [ getDependencies f
        , S.unions $ getDependencies <$> args
        ]
      PAppArr _ f args -> S.unions
        [ getDependencies f
        , S.unions $ getDependencies <$> args
        ]
      OfHigherPostfixPrec a -> getDependencies a
    | Just Refl <- matches @8 (sing @n)
    = case e of
      PPower _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      OfHigher8 a -> getDependencies a
    | Just Refl <- matches @7 (sing @n)
    = case e of
      PMul _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PDiv _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PMod _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      OfHigher7 a -> getDependencies a
    | Just Refl <- matches @6 (sing @n)
    = case e of
      PPlus _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PMinus _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      OfHigher6 a -> getDependencies a
    | Just Refl <- matches @4 (sing @n)
    = case e of
      PLT _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PLTEQ _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PGT _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PGTEQ _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PEQ _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      PNEQ _ a b -> S.unions
        [ getDependencies a
        , getDependencies b
        ]
      OfHigher4 a -> getDependencies a

    | Just Refl <- matches @1 (sing @n)
      = case e of
        PLambda _ args _ body
          -> getDependencies body `S.difference` S.unions (getDependencies . fst <$> args)
        OfHigher1 a
          -> getDependencies a
    | Just Refl <- matches @0 (sing @n)
      = case e of
        OfHigher0 a
          -> getDependencies a



    | otherwise
    = error "getDependencies: Unmatched EPrec"

instance GetDependencies (A0 ctx) where
  getDependencies a = case a of
    Decl _ v e _ -> getDependencies e `S.difference` getDependencies v
    Assign v e _ -> getDependencies e `S.difference` getDependencies v
    Print e _ -> getDependencies e
    SysCommand _ _ -> S.empty


instance SingI n => GetVar (EPrec ctx n) where
  getVar e
    | Just Refl <- matches @Atom (sing @n)
    = case e of
      PVar _ s -> S.singleton s
      PTuple _ a b xs -> S.unions $  [getVar x | x <- (a : b : xs)]
      PParen _ a -> getVar a
      PDefer _ _ -> S.empty
      PIf _ _ -> S.empty
      PInt _ _ -> S.empty
      PFloat _ _ -> S.empty
      PBool _ _ -> S.empty
      PString _ _ -> S.empty

    | Just Refl <- matches @PrefixPrec (sing @n)
    = case e of
      PUMinus _ _ -> S.empty
      OfHigherPrefixPrec a -> getVar a

    | Just Refl <- matches @PostfixPrec (sing @n)
    = case e of
      PApp _ _ _ -> S.empty
      PAppArr _ _ _ -> S.empty
      OfHigherPostfixPrec a -> getVar a

    | Just Refl <- matches @8 (sing @n)
    = case e of
      PPower _ _ _ -> S.empty
      OfHigher8 a -> getVar a

    | Just Refl <- matches @7 (sing @n)
    = case e of
      PMul _ _ _ -> S.empty
      PDiv _ _ _ -> S.empty
      PMod _ _ _ -> S.empty
      OfHigher7 a -> getVar a

    | Just Refl <- matches @6 (sing @n)
    = case e of
      PPlus _ _ _ -> S.empty
      PMinus _ _ _ -> S.empty
      OfHigher6 a -> getVar a

    | Just Refl <- matches @4 (sing @n)
    = case e of
      PLT _ _ _ -> S.empty
      PLTEQ _ _ _ -> S.empty
      PGT _ _ _ -> S.empty
      PGTEQ _ _ _ -> S.empty
      PEQ _ _ _ -> S.empty
      PNEQ _ _ _ -> S.empty
      OfHigher4 a -> getVar a
    | Just Refl <- matches @1 (sing @n)
      = case e of
        PLambda _ _ _ _ -> S.empty
        OfHigher1 a -> getVar a
    | Just Refl <- matches @0 (sing @n)
      = case e of
        OfHigher0 a -> getVar a
    | otherwise
    = error "getVar: Unmatched EPrec"

instance GetVar (A0 ctx) where
  getVar a = case a of
    Decl _ v _ _ -> getVar v
    Assign v _ _ -> getVar v
    Print _ _ -> S.empty
    SysCommand _ _ -> S.empty

instance IsStaticallyConstructive (A0 ctx) where
  isStaticallyConstructive a = case a of
    Decl _ _ e _ -> isStaticallyConstructive e
    Assign _ e _ -> isStaticallyConstructive e
    Print _ _ -> True
    SysCommand _ _ -> True

instance SingI n => IsStaticallyConstructive (EPrec ctx n) where
  isStaticallyConstructive e
    | Just Refl <- matches @Atom (sing @n)
    = case e of
      PVar _ _ -> False
      PTuple _ a b xs
        -> all isStaticallyConstructive $ a : b : xs
      PParen _ a -> isStaticallyConstructive a
      PDefer _ _ -> True
      PIf _ _ -> False
      PInt _ _ -> True
      PFloat _ _ -> True
      PBool _ _ -> True
      PString _ _ -> True

    | Just Refl <- matches @PrefixPrec (sing @n)
    = case e of
      PUMinus _ _ -> False
      OfHigherPrefixPrec a -> isStaticallyConstructive a

    | Just Refl <- matches @PostfixPrec (sing @n)
    = case e of
      PApp _ _ _ -> False
      PAppArr _ _ _ -> False
      OfHigherPostfixPrec a -> isStaticallyConstructive a

    | Just Refl <- matches @8 (sing @n)
    = case e of
      PPower _ _ _ -> False
      OfHigher8 a -> isStaticallyConstructive a

    | Just Refl <- matches @7 (sing @n)
    = case e of
      PMul _ _ _ -> False
      PDiv _ _ _ -> False
      PMod _ _ _ -> False
      OfHigher7 a -> isStaticallyConstructive a

    | Just Refl <- matches @6 (sing @n)
    = case e of
      PPlus _ _ _ -> False
      PMinus _ _ _ -> False
      OfHigher6 a -> isStaticallyConstructive a
    | Just Refl <- matches @4 (sing @n)
    = case e of
      PLT _ _ _ -> False
      PLTEQ _ _ _ -> False
      PGT _ _ _ -> False
      PGTEQ _ _ _ -> False
      PEQ _ _ _ -> False
      PNEQ _ _ _ -> False
      OfHigher4 a -> isStaticallyConstructive a
    | Just Refl <- matches @1 (sing @n)
      = case e of
        PLambda _ _ _ _ -> True
        OfHigher1 a -> isStaticallyConstructive a
    | Just Refl <- matches @0 (sing @n)
      = case e of
        OfHigher0 a -> isStaticallyConstructive a
    | otherwise
    = error "isStaticallyConstructive: Unmatched EPrec"
