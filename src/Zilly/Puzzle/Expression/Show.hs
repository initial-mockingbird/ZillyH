{-# LANGUAGE LambdaCase            #-}
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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans          #-}


module Zilly.Puzzle.Expression.Show
  ( Show
  ) where

import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Expression.Patterns
import Utilities.ShowM
import Zilly.Puzzle.Environment.TypedMap
import Data.Array
import Data.List (intercalate)
import Zilly.Puzzle.Patterns.Exports

showRange :: Show a => (a,Maybe a) -> String
showRange (a, Nothing) = show a
showRange (a, Just b) = show a <> " .. " <> show b

instance Show (E ctx) where
  showsPrec p = \case
    ValZ  n -> showString (show n)
    ValF  n -> showString (show n)
    ValB  s -> showString (show s)
    ValS  s -> showString (show s)
    Var  _ x -> showsPrec p . UT . varNameM $ x
    MkArray _ xs ->  showString (prettyArray xs)
    ArraySlice _ a b -> shows a . showList ([ UT $ showRange r | r <- b])
    If _ c t f -> showParen (p > 10) $ showString "if( " . shows c . showString ", " . shows t . showString ", " . shows f . showString ")"
    Lambda _ (at,mt)  x t ->  showParen (p > 9)
      $ showString "λ("
      . shows at
      . showString " "
      . shows (UT $ varNameM  x)
      . showString ")"
      . showString (maybe ""  (mappend " => " . show) mt)
      . showString " -> " .  shows t
    LambdaC _ (at,mt) _ x t -> showParen (p > 9)
      $  showString "λ( "
      . shows at
      . showString " "
      . shows (UT $ varNameM  x)
      . showString ")"
      . showString (maybe "" (mappend " => " . show) mt)
      . showString " -> " .  shows t
    MinusInfix' a b
      -> showParen (p > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
    PlusInfix' a b
      -> showParen (p > 6) $ showsPrec 6 a . showString " + " . showsPrec 7 b
    TimesInfix' a b
      -> showParen (p > 7) $ showsPrec 7 a . showString " * " . showsPrec 8 b
    DivInfix' a b
      -> showParen (p > 7) $ showsPrec 7 a . showString " / " . showsPrec 8 b
    PowInfix' a b
      -> showParen (p > 8) $ showsPrec 9 a . showString " ^ " . showsPrec 8 b
    AppendInfix' a b
      -> showParen (p > 6) $ showsPrec 6 a . showString " ++ " . showsPrec 7 b
    AndInfix' a b
      -> showParen (p > 3) $ showsPrec 4 a . showString " && " . showsPrec 3 b
    OrInfix' a b
      -> showParen (p > 3) $ showsPrec 4 a . showString " || " . showsPrec 3 b
    SubtractSat' a b
      -> showParen (p > 6) $ showsPrec 6 b . showString " - " . showsPrec 7 a
    LTInfix' a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " < " . showsPrec 5 b
    LEInfix' a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " <= " . showsPrec 5 b
    GTInfix' a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " > " . showsPrec 5 b
    GEInfix' a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " >= " . showsPrec 5 b
    EQInfix' a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " = " . showsPrec 5 b
    NEInfix' a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " <> " . showsPrec 5 b
    Negate' a -> showParen (p > 11) $ showString "~" . showsPrec 11 a
    MinusU' a -> showParen (p > 11) $ showString "-" . showsPrec 11 a

    App  _ f a -> showParen (p > 10) $ showsPrec 10 f . showChar '(' . shows a . showChar ')'
    Defer _ v -> showString "'" . shows v . showString "'"
    LazyC _ _ e _ -> showsPrec p e -- showChar '<' . showsPrec 10 e . showString  ", " . showsPrec 10 env . showChar '>'
    Bottom _ _ _-> showString "⊥"
    MkTuple _ a b _ -> showString "(" . shows a . showString ", " . shows b . showString ")"
    DotApp _ a b -> shows a . showString "." . showString b
    Cons _ n xs -> showString n . showChar '(' . showString (intercalate "," $ show <$> xs) . showChar ')'
    ConsV t n xs -> shows (Cons t n xs)
    ARecord _ fields
      -> showString "{ "
      . showString (intercalate ", " [ n <> ": " <> show v | (n,v) <- fields])
      . showString " }"
    ARecordV t fields -> shows (ARecord t fields)
    Match _ a branches
      -> showString "match " . shows a . showString " with "
      . showString (intercalate "\n | " [ showPattern show p <> " -> " <> show e | (p,e) <- branches])
