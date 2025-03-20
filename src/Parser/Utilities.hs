{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
Module      : ParsecT String u m.Utilities
Description : General parsing utilities for BNF grammars
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Based on 

Design Patterns for ParsecT String u m Combinators (Functional Pearl)

ACM ISBN 978-1-4503-8615-9/21/08.
https://doi.org/10.1145/3471874.3472984
-}
module Parser.Utilities where


import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Data.String (IsString(..))
import Control.Monad
import Control.Applicative ((<**>))
import Data.Functor.Const

import Data.Functor
import Data.Functor.Identity




-------------------------------
-- Main combinators
-------------------------------

lexeme :: Monad m => ParsecT String u m a -> ParsecT String u m a
lexeme p = p <* spaces

fully :: Monad m => ParsecT String u m a -> ParsecT String u m a
fully p = spaces *> p <* eof

token :: Monad m => ParsecT String u m a -> ParsecT String u m a
token = lexeme . try

keyword :: Monad m => String -> ParsecT String u m ()
keyword k = token (string k *> notFollowedBy alphaNum)

{- anyKeyword :: ParsecT String u m ()
anyKeyword = choice $ map keyword keywords -}

infixl1 :: (a -> b) -> ParsecT String u m a -> ParsecT String u m (b -> a -> b) -> ParsecT String u m b
infixl1 wrap p op = (wrap <$> p) <**> rest
  where rest = flip (.) <$> (flip <$> op <*> p) <*> rest <|> pure id

infixr1 :: (a -> b) -> ParsecT String u m a -> ParsecT String u m (a -> b -> b) -> ParsecT String u m b
infixr1 wrap p op =
  p <**> (flip <$> op <*> infixr1 wrap p op <|> pure wrap)

postfix :: (a -> b) -> ParsecT String u m a -> ParsecT String u m (b -> b) -> ParsecT String u m b
postfix wrap p op = (wrap <$> p) <**> rest
  where rest = flip (.) <$> op <*> rest <|> pure id

prefix :: (a -> b) -> ParsecT String u m (b -> b) -> ParsecT String u m a -> ParsecT String u m b
prefix wrap op p = op <*> prefix wrap op p <|> wrap <$> p

parens :: Monad m => ParsecT String u m a -> ParsecT String u m a
parens = lexeme . between (token $ char '(') (token $ char ')')
    
quoted :: Monad m => ParsecT String u m a -> ParsecT String u m a
quoted = lexeme . between (token $ char '\'') (token $ char '\'')

bracketed :: Monad m => ParsecT String u m a -> ParsecT String u m a
bracketed = lexeme . between (char '<') (char '>')

bracketed' :: Monad m => ParsecT String u m a -> ParsecT String u m a
bracketed' = lexeme . between (char '[') (char ']')

---------------------------------------------
-- Fixity, Associativity and Precedence
---------------------------------------------

data Fixity a b sig where
  InfixL  :: Fixity a b (b -> a -> b) 
  InfixR  :: Fixity a b (a -> b -> b) 
  InfixN  :: Fixity a b (a -> a -> b) 
  Prefix  :: Fixity a b (b -> b) 
  Postfix :: Fixity a b (b -> b)

data Op u m a b where
  Op :: Fixity a b sig -> (a -> b) -> ParsecT String u m sig -> Op u m a b

data Prec u m a where
  Level :: Prec u m a   -> Op u m a b -> Prec u m b
  Atom  :: ParsecT String u m a -> Prec u m a

infixl 5 >-|
infixr 5 |-<
(>-|) :: Prec u m a -> Op u m a b -> Prec u m b
(>-|) = Level 

(|-<) :: Op u m a b -> Prec u m a -> Prec u m b
(|-<) = flip (>-|)

class sub < sup where
  upcast :: sub -> sup
  downcast :: sup -> Maybe sub

transUpcast :: forall b a c. (a < b, b < c) => a -> c
transUpcast = upcast . upcast @a @b

-----------------------------------------
-- Precedence and Associativity
-----------------------------------------

precedence :: Prec u m a -> ParsecT String u m a
precedence (Atom atom') = atom'
precedence (Level lvls ops') = con (precedence lvls) ops'
  where 
    con :: ParsecT String u m a -> Op u m a b -> ParsecT String u m b
    con p (Op InfixL wrap op)  = infixl1 wrap p op
    con p (Op InfixR wrap op)  = infixr1 wrap p op
    con p (Op InfixN wrap op)  = p <**> (flip <$> op <*> p <|> pure wrap)
    con p (Op Prefix wrap op)  = prefix wrap op p
    con p (Op Postfix wrap op) = postfix wrap p op

precHomo :: ParsecT String u m a -> [Op u m a a] -> ParsecT String u m a
precHomo atom' = precedence . foldl (>-|) (Atom atom')


gops :: Monad m => Fixity a b sig -> (a -> b) -> [ParsecT String u m sig] -> Op u m a b
gops fixity wrap = Op fixity wrap . choice

ops :: Monad m => Fixity a a sig -> [ParsecT String u m sig] -> Op u m a a
ops fixity = gops fixity id

sops :: (a < b, Monad m) => Fixity a b sig -> [ParsecT String u m sig] -> Op u m a b
sops fixity = gops fixity upcast

----------------
-- Misc ParsecT String u ms
----------------

mkIdent :: Monad m => ParsecT String u m () -> ParsecT String u m String
mkIdent anyKeyword
  =  notFollowedBy anyKeyword *> mzero
  <|> lexeme (f <$> (char '_' <|> letter) <*> many (letter <|> digit <|> char '_'))
  where f c cs = c:cs




number :: Monad m => ParsecT String u m Int
number = f <$> option "" (token $ string "-" ) <*> lexeme (many1 digit)
  where f "-" ds = read ('-':ds)
        f _   ds = read ds
