{-# LANGUAGE ImportQualifiedPost #-}

module Zilly.Puzzle.Types.Morphisms
  ( rtype
  , isSuperTypeOf
  , isSubtypeOf
  , upperBound
  , lowerBound
  , unsafeUpperBound
  , unsafeLowerBound
  ) where

import Zilly.Puzzle.Types.Types
import Zilly.Puzzle.Types.Patterns
import Data.Map (Map)
import Data.Map qualified as M
import Control.Monad (join, zipWithM)
import Data.Maybe (isJust)
import Zilly.Puzzle.Types.Show ()
import Data.Functor.Compose

rtype :: Types -> Types
rtype (Lazy a) = a
rtype (a :-> b) = a :-> b
rtype (NDArray n a) = NDArray n (rtype a)
rtype rec@(ARecord {}) = rec
rtype (TCon n xs) = TCon n (rtype <$> xs)
rtype (TVar a) =  RV . TVar $ a
rtype (RV x) = case x of
  TVar a       -> RV . RV $ TVar a
  RV y        -> rtype $ rtype (RV y)
  TFamApp n y ys -> RV $ TFamApp n y ys
  _ -> rtype $ rtype x
rtype (TFamApp n x xs) = RV $ TFamApp n x xs


isSuperTypeOf :: Types -> Types -> Bool
isSuperTypeOf a b = isJust $ upperBound a b

isSubtypeOf :: Types -> Types -> Bool
isSubtypeOf a b = isJust $ lowerBound a b

upperBoundM :: Applicative m => m Name -> Types -> Types -> m (Maybe Types)
upperBoundM _ a b | a == b = pure $ Just a
upperBoundM fresh (a :-> b) (c :-> d) = getCompose $
  (:->) <$> Compose (lowerBoundM fresh a c) <*> Compose (upperBoundM fresh b d)

upperBoundM _ _ _ = undefined

lowerBoundM :: Applicative m => m Name -> Types -> Types -> m (Maybe Types)
lowerBoundM = undefined


upperBound :: Types -> Types -> Maybe Types
upperBound a b | a == b = Just a
upperBound (a :-> b) (c :-> d) = (:->) <$> lowerBound a c <*> upperBound b d
upperBound (NDArray n a) (NDArray m b)
  | n == m    = NDArray n <$> upperBound a b
  | otherwise = Nothing
upperBound (Lazy a) (Lazy b) = Lazy <$> upperBound a b
upperBound Z F = Just F
upperBound F Z = Just F
upperBound (NTuple a b xs) (NTuple c d ys)
  | length xs == length ys = NTuple <$> upperBound a c <*> upperBound b d <*> zipWithM upperBound xs ys
  | otherwise              = Nothing
upperBound Top _ = Just Top
upperBound _ Top = Just Top
upperBound Bot a = Just a
upperBound a Bot = Just a
upperBound (Lazy a) b = Lazy <$> upperBound a b
upperBound a (Lazy b) = Lazy <$> upperBound a b
upperBound ZInfer a = Just a
upperBound a ZInfer = Just a
upperBound (ARecord a) (ARecord b)
  = let amap   = M.fromList a
        bmap   = M.fromList b
        mabmap = M.unionWith (\ma mb -> join $ upperBound <$> ma <*> mb) (pure <$> amap) (pure <$> bmap)
        record = ARecord . M.toList <$> sequence mabmap
  in record
upperBound (TVar _) b = Just b
upperBound a (TVar _) = Just a
upperBound (RV x) a = upperBound (rtype x) a
upperBound a (RV x) = upperBound a (rtype x)
upperBound _ _ = Nothing

lowerBound :: Types -> Types -> Maybe Types
lowerBound a b | a == b = Just a
lowerBound (a :-> b) (c :-> d) = (:->) <$> upperBound a c <*> lowerBound b d
lowerBound (NDArray n a) (NDArray m b)
  | n == m    = NDArray n <$> lowerBound a b
  | otherwise = Nothing
lowerBound (Lazy a) (Lazy b) = Lazy <$> lowerBound a b
lowerBound Z F = Just Z
lowerBound F Z = Just Z
lowerBound (NTuple a b xs) (NTuple c d ys)
  | length xs == length ys = NTuple <$> lowerBound a c <*> lowerBound b d <*> zipWithM lowerBound xs ys
  | otherwise              = Nothing
lowerBound Bot _ = Just Bot
lowerBound _ Bot = Just Bot
lowerBound Top a = Just a
lowerBound a Top = Just a
lowerBound (Lazy a) b = lowerBound a b
lowerBound a (Lazy b) = lowerBound a b
lowerBound ZInfer a = Just a
lowerBound a ZInfer = Just a
lowerBound (ARecord a) (ARecord b)
  = let amap   = M.fromList a
        bmap   = M.fromList b
        mabmap = M.intersectionWith (\ma mb -> join $ lowerBound <$> ma <*> mb) (pure <$> amap) (pure <$> bmap)
        record = ARecord . M.toList <$> sequence mabmap
  in record
lowerBound (TVar _) b = Just b
lowerBound a (TVar _) = Just a
lowerBound (RV x) a = lowerBound (rtype x) a
lowerBound a (RV x) = lowerBound a (rtype x)
lowerBound _ _ = Nothing

unsafeUpperBound :: Types -> Types -> Types
unsafeUpperBound a b = case upperBound a b of
  Just t  -> t
  Nothing -> error $ "No upper bound for types: " <> show a <> " and " <> show b

unsafeLowerBound :: Types -> Types -> Types
unsafeLowerBound a b = case lowerBound a b of
  Just t  -> t
  Nothing -> error $ "No lower bound for types: " <> show a <> " and " <> show b
