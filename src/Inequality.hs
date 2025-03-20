{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

-- https://stackoverflow.com/questions/6939043/is-it-possible-to-place-inequality-constraints-on-haskell-type-variables
module Inequality ((:/~)) where

-- The following code is my own hacked modifications to Oleg's original TypeEq. Note
-- that his TypeCast class is no longer needed, being basically equivalent to ~.

data Yes = Yes deriving (Show)
data No = No deriving (Show)

class (TypeEq x y No) => (:/~) x y
instance (TypeEq x y No) => (:/~) x y

class (TypeEq' () x y b) => TypeEq x y b 
instance (TypeEq' () x y b) => TypeEq x y b 


class TypeEq' q x y b | q x y -> b 
instance (b ~ Yes) => TypeEq' () x x b 
instance (b ~ No) => TypeEq' q x y b 

