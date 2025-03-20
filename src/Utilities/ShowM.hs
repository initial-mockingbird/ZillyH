{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module      : Utilities.ShowM
Description : A monadic show class
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Defines a show class that can perform arbitrary monadic actions.

Super useful when you want to read MVars.
-}
module Utilities.ShowM where
import Control.Monad


newtype UnquotedText = UT String

instance Show UnquotedText where
  show (UT s) = s

newtype I a = I { unI :: a }

instance Functor I where
  fmap f (I x) = I (f x)


type ShowSM m = String -> m String

class Functor f => ShowM f a where
  {-# MINIMAL showsPrecM | showM #-}
  showM :: a -> f String
  showsPrecM :: Int -> a -> ShowSM f

  showM        x   = showsM x ""
  showsPrecM _ x s = (<> s) <$> showM x 
  

-- | equivalent to 'showsPrec' with a precedence of 0.
showsM :: (ShowM f a) => a -> ShowSM f
showsM =  showsPrecM 0

showCharM :: Applicative f => Char -> ShowSM f
showCharM c = pure <$> (c :)


showParenM :: Monad m => Bool -> ShowSM m -> ShowSM m
showParenM b p =  if b then showCharM '(' <=< p <=< showCharM ')' else p 

showStringM :: Applicative m => String -> ShowSM m
showStringM x =  pure . (x ++)

instance Applicative f => ShowM f Int where
  showM = pure . show

instance Applicative f => ShowM f UnquotedText where
  showM (UT s) = pure s

{-   
instance Show a => ShowM I a where
  showM = I . show   -}