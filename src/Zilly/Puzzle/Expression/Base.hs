{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE GADTs                 #-}

{-|
Module      : Zilly.ADT.Expression
Description : Main Expression Tree a la Trees that grow for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Check
@@
@article{najd2016trees,
  title={Trees that grow},
  author={Najd, Shayan and Jones, Simon Peyton},
  journal={arXiv preprint arXiv:1610.04799},
  year={2016}
}
@@
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf

-}
module Zilly.Puzzle.Expression.Base
  ( E (..)
  , LambdaCtx
  , LambdaCCtx
  , LambdaTag
  , LambdaCTag
  , EvalError (..)
  ) where

import Zilly.Puzzle.Types.Exports
import Zilly.Puzzle.Environment.TypedMap
import Data.Kind (Type)
import Zilly.Puzzle.Effects.Memoize
import Data.Array




{-| Zilly expression Language. |-}
data  E  (ctx :: Type) where
  ValZ      :: Int -> E ctx
  ValF      :: Double -> E ctx
  ValB      :: Bool -> E ctx
  ValS      :: String -> E ctx
  Var      :: LensM (E ctx) -> E ctx
  If       :: E ctx -> E ctx  -> E ctx -> E ctx
  Lambda   :: (Types,Maybe Types) -> LensM (E ctx) -> E ctx -> E ctx
  Defer    :: E ctx  -> E ctx
  App      :: E ctx -> E ctx -> E ctx
  LambdaC  :: (Types, Maybe Types) -> TypeRepMap (E ctx) -> LensM (E ctx) -> E ctx  -> E ctx
  LazyC    :: TypeRepMap (E ctx) -> E ctx ->  Memoized (EvalMonad (E ctx)) (E ctx) -> E ctx
  MkTuple  :: E ctx -> E ctx -> [E ctx] -> E ctx
  MkArray  :: Array (E ctx) -> E ctx
  Bottom   :: EvalError -> [EvalError] -> E ctx
  ArraySlice :: E ctx -> [(E ctx,Maybe (E ctx))] -> E ctx

type family LambdaCtx  (ctx :: Type) :: Type
type family LambdaCCtx (ctx :: Type) :: Type

data LambdaTag
data LambdaCTag

data EvalError
  = TypeMismatch String
  | DivisionByZero
  | OutOfBounds String
  | OtherError String
  deriving (Eq, Show)
