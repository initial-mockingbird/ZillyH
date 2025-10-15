{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ImportQualifiedPost   #-}


module Zilly.Puzzle.Action.Interpreter
  ( AEffects
  , ACtxConstraint
  , evalA'
  , evalA
  , evalProgram
  ) where

import Zilly.Puzzle.Action.Base
import Zilly.Puzzle.Expression.Exports
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Effects.CC
import Data.Default
import Control.Monad.Error.Class
import Zilly.Puzzle.Effects.Block (CCActions(..))
import Data.Traversable
import Data.Array qualified as A

type AEffects m =
  ( Effects m
  , MonadCC m
  , CCActions m
  -- , CCActions m
  )

type ACtxConstraint ctx m =
  ( CtxConstraint ctx m
  , AEffects m
  , Default (m (TypeRepMap (E ctx)))

  )

evalA' :: forall {m} ctx.
  ( ACtxConstraint ctx m
  )
  => (E ctx -> m (E ctx)) -> A ctx -> m (TypeRepMap (E ctx), A ctx)
evalA' evalE a = fmap (a,) getQ >>= \case
  (Print _, 0) -> do
    (env,result) <- evalA evalE a
    pure (env, result)
  (Print _, 1) -> do
    cycleCC
    (env,result) <- evalA evalE a
    putQ 0
    pure (env, result)

  (Reassign {},0) -> do
    (env, result) <- evalA evalE a
    cycleCC
    putQ 0
    pure (env, result)
  (Reassign {},1) -> do
    cycleCC
    (env, result) <- evalA evalE a
    cycleCC
    putQ 0
    pure (env, result )
  (SysCommand "tick", _) -> do
    cycleCC
    putQ 0
    evalA evalE a
  (SysCommand "reset", _) -> do
    res <- evalA evalE a
    cycleCC
    putQ 0
    pure res
  (Assign {}, _) -> do
    (env, a') <- evalA evalE a
    putQ 1
    pure (env,a')
  _ -> evalA evalE a



evalA :: forall {m} ctx.
  (ACtxConstraint ctx m)
  => (E ctx -> m (E ctx)) -> A ctx -> m (TypeRepMap (E ctx), A ctx)
evalA evalE (Print a) = evalE a >>= \case
  a' -> getEnv >>= \env -> pure  (env, Print a')
evalA evalE a@(Assign ltype x y) = do
  env1' <- getEnv
  -- env1' <- declare @(Ftype ltype) (varNameM x) env0
  withEnv @(E ctx) env1' $ evalE y >>= \a' -> do
      env <- getEnv
      (\env' -> (env',a)) <$> setM x a' ltype env

evalA evalE a@(Reassign x [] y) = evalE y >>= \a' -> do
  env <- getEnv
  md <- varMetadata x env
  (\env' -> (env',a)) <$> setM x a' md env
evalA evalE a@(Reassign x (eis:eiss) y) = evalE y >>= \case
  y0 ->  do
    let y = A.scalar y0
    ixs <- for (eis:eiss) $ \eixs -> for eixs $ \(l,u) -> (,) <$> evalE l <*> traverse evalE u >>= \case
      (ValZ l', Just (ValZ u')) -> pure (l', Just u')
      (ValZ l', Nothing) -> pure (l', Nothing)
      (a',b') -> throwError
        $ "Error on evaling 'arraySlice' expression. Unsupported index: "
        <> show a' <> " and " <> show b'

    env <- getEnv
    md <- varMetadata x env
    xv <- getL x env
    case xv of
      MkArray arr -> do
        let unravel (MkArray arr) = arr
            unravel e = A.fromList [] [e]
        let
            sliceUnravel :: [(Int, Maybe Int)] -> A.Array (E ctx) -> A.Array (E ctx)
            sliceUnravel ixs arr =
              let new = A.slice' ixs arr
              in if null (A.shapeL new)
                then unravel (A.unScalar new)
                else new
        let
            update :: [[(Int, Maybe Int)]] -> A.Array (E ctx) -> A.Array (E ctx)
            -- update [ixs] current = A.updateSlice current ixs $ A.scalar y
            update (ixs:ixss) current = case update ixss (sliceUnravel ixs current) of
              updated | null (A.shapeL updated)
                -> A.updateSlice (current) ixs $ updated
              updated
                -> A.updateSlice current ixs $ A.scalar $ MkArray updated
            update [] _ = y



        -- [ixs0,ixs1,ixs2]
        -- slice' ixs0 arr0 & \arr1 ->
        -- slice' ixs1 arr1 & \arr2 ->
        -- slice' ixs2 arr2 &
        let arr' =  update ixs arr
        (\env' -> (env',a)) <$> setM x (MkArray arr') md env
      v -> throwError $ "reassigning non-array variable: " <> show v



evalA _ a@(SysCommand "reset") = do
  env <- def @(m (TypeRepMap (E ctx)))
  pure  (env,a)
evalA _ a@(SysCommand "tick") = do
  env <- getEnv
  pure  (env,a)

evalA evalE (SysCommand _) = evalA evalE ABottom
evalA _ ABottom = error "trying to eval action bottom"

evalProgram :: forall {m} ctx.
  ( ACtxConstraint ctx m
  )
  => (E ctx -> m (E ctx)) -> [A ctx] -> m ((TypeRepMap (E ctx) ,[A ctx]))
evalProgram _ []     = getEnv >>= \env -> pure ((env, []))
evalProgram evalE (x:xs) = evalA' @ctx evalE x >>= \(env',x') -> fmap (x' :) <$> withEnv env' (evalProgram evalE xs)
