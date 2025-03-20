{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
-- https://stackoverflow.com/questions/6939043/is-it-possible-to-place-inequality-constraints-on-haskell-type-variables
module InequalityFamily  where



type family TypeEq (x :: k) (y :: k) :: Bool where
  TypeEq x x  = True 
  TypeEq x y  = False 


class (False ~ TypeEq x y) => (:/~) (x :: k) (y :: k)
instance (False ~ TypeEq x y) => (:/~) (x :: k) (y :: k)
