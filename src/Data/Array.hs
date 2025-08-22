{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array
  ( module AD
  , slice'
  , updateSlice
  , prettyArray
  , t0
  , t1
  , t3

  ) where

import Data.Array.Dynamic qualified as AD
import Data.Array.Dynamic
import Data.Traversable
import Data.Maybe (fromMaybe, catMaybes)
import Debug.Trace (trace)
import Data.List (intercalate)


zipWithPadRight :: [a] -> [b] -> (a -> b -> c) -> (b -> c) -> [c]
zipWithPadRight [] ys _ g = g <$> ys
zipWithPadRight _ [] f _  = []
zipWithPadRight (x:xs) (y:ys) f g =
  f x y : zipWithPadRight xs ys f g

slice' :: [(Int,Maybe Int)] -> Array a  -> Array a
slice' sixs arr
  =  let slices = map (\(i,mj) -> (i, fromMaybe i mj - i + 1 )) sixs
  in let newShape = catMaybes $ zipWithPadRight sixs (shapeL arr)
          (\(l, mu) _ -> fmap (\u -> u - l + 1) mu)
          pure
  in reshape newShape $ slice slices arr

updateSlice :: Array a -> [(Int,Maybe Int)] -> Array a -> Array a
updateSlice arr sixs newArr
  = update arr
  $ indexArray' newArr
  $ (\(l,mu) -> (l, fromMaybe l mu)) <$>  sixs

indexArray :: Array a -> Array ([Int],a)
indexArray arr =
  let shape = shapeL arr
  in let indexes  = genIndexes shape
  in fromList shape . zip indexes . toList $ arr

genIndexes :: [Int] -> [[Int]]
genIndexes ixs = case ixs of
  (x:xs) -> do
        i  <- [(0 :: Int)..(x-1)]
        rest   <- genIndexes xs
        pure $ i :  rest
  [] -> pure []

genIndexes' :: [(Int,Int)] -> [[Int]]
genIndexes' ixs = case ixs of
  ((l,u):xs) -> do
        i  <- [l..u]
        rest   <- genIndexes' xs
        pure $ i :  rest
  [] -> pure []

indexArray' :: Array a -> [(Int,Int)] -> [([Int],a)]
indexArray' arr ixs =
  let indexes  = genIndexes' ixs
  in zip indexes . toList $ arr

prettyArray :: forall a. Show a => Array a -> String
prettyArray arr = prettyList shape elems
  where
    shape :: [Int]
    shape = shapeL arr
    elems :: [a]
    elems = toList arr

    splitEvery :: Int -> [a] -> [[a]]
    splitEvery _ [] = []
    splitEvery n xs = take n xs : splitEvery n (drop n xs)

    prettyList :: [Int] -> [a] -> String
    prettyList []  as = show as
    prettyList [_] as = show as
    prettyList (x:xs) as
      = "[ "
      <> (intercalate ", "  . fmap (prettyList xs) . splitEvery (product xs)) as
      <> " ]"

t0 :: Array Int
t0 = fromList [2,3,3] [1..(2*3*3)]

t1 :: Array Int
t1 = fromList [2,2] [10..(10+2*2) - 1]

t3 :: Array Int
t3 = fromList [1,2,2] [10..(10+1*2*2) - 1]
