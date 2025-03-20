{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-|
Module      : Utilities.LensM
Description : "Lenses" that perform monadic actions
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

We use "lens" very loosely here, since whenever you add arbitrary
monadic actions to lenses, it's very hard to keep the lens laws.

In our case, a LensM will eventually embody a means to
represent a variable in a context \(\Gamma\):

- We can read it using @getL@
- We can set it using @setL@, yielding an error for already defined variables
- We can set it fresh using @setFL@, ignoring if it's already defined or not.
- We can get the variable name by using @varNameM@

If we introduce algebraic effects into the mix, we can encode these
axioms (i.e: adding a @ReadOnly@ effect for @getL@). But for the
time being, this isn't a pressing issue.

-}
module Utilities.LensM where
import Data.Kind (Type)
import Control.Monad.Reader

type family Gamma (m :: Type -> Type) :: Type

-- Defines a way to get, set, set fresh and obtain the name of a variable
data LensM (m :: Type -> Type) (a :: Type) = LensM
  { getL  ::  Gamma m -> m a
  , setL  ::  Gamma m -> a -> m (Gamma m)
  , setFL ::  Gamma m -> a -> m (Gamma m)
  , varNameM :: String
  }

viewM ::LensM m a -> Gamma m -> m a
viewM  = getL

setM :: LensM m a -> a -> Gamma m -> m (Gamma m)
setM = flip . setL

setMF :: LensM m a -> a -> Gamma m -> m (Gamma m)
setMF = flip . setFL
