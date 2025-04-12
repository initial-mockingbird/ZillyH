{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NamedFieldPuns #-}
module Zilly.Runner where

import Zilly.Classic.Runner qualified as Classic
import Zilly.Unsugared.Runner qualified as Unsugared
import Text.Parsec
import Data.Functor.Identity
import Data.String (IsString(..))
import Zilly.Unsugared.Parsing.Utilities qualified as PU
import Control.Monad (void)
import Control.Applicative ((<*))
import Data.Functor ((<$), ($>))
import Control.Concurrent.MVar
import System.IO.Error
import Data.Foldable (traverse_)
import Control.Monad ((<=<))

type Parser a = ParsecT String () Identity a
data InterpretMode = ClassicInterpreter |  UnsugaredInterpreter deriving Eq


-------------------------------
-- Useful Orphans
-------------------------------

instance u ~ () => IsString (Parser u ) where
  fromString str = void $ PU.token (string str)



parseChange :: Parser (Maybe InterpretMode)
parseChange
  =   "::zilly+" <* (spaces *> eof) $> Just ClassicInterpreter
  <|> "::zilly"  <* (spaces *> eof)  $> Just UnsugaredInterpreter
  <|> pure Nothing
  <?> "Special command not recognized. Expected either ::zilly or ::zilly+"

data UIST = UIST
  { process :: String -> IO String
  , currentMode :: InterpretMode
  }

buildUniversalInterpreter :: IO (String -> IO String )
buildUniversalInterpreter =  do
  f <- Unsugared.buildInterpreter
  let iST = UIST{process = f, currentMode =UnsugaredInterpreter}
  mst <- newMVar iST
  pure $ \s -> flip catchIOError (\e -> pure ("Error: " <> show e)) $ do
    st <- takeMVar mst
    (s',newST) <- interpret st s
    putMVar mst newST
    pure s'

interpret :: UIST -> String -> IO (String, UIST)
interpret st@(UIST{process,currentMode}) s = case runParser parseChange () "" s of
    Left e -> pure ("Error: " <> show e, st)
    Right Nothing -> process s >>= \s' -> pure (s',st)
    Right (Just newMode) -> case newMode of
      UnsugaredInterpreter -> do
        f' <- Unsugared.buildInterpreter
        pure ("ACK: " <> s <> " ==> " <> "Interpreter mode changed.",UIST f' UnsugaredInterpreter)
      ClassicInterpreter -> do
        f' <- Classic.buildInterpreter
        pure ("ACK: " <> s <> " ==> " <> "Interpreter mode changed.", UIST f' ClassicInterpreter)




ex0 :: IO ()
ex0 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/equality.z"
  traverse_ (putStrLn <=< i) fc


ex1 :: IO ()
ex1 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/comparison.z"
  traverse_ (putStrLn <=< i) fc

ex2 :: IO ()
ex2 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/lazy1.z"
  traverse_ (putStrLn <=< i) fc

ex3 :: IO ()
ex3 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/lazy2.z"
  traverse_ (putStrLn <=< i) fc

ex4 :: IO ()
ex4 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/functions.z"
  traverse_ (putStrLn <=< i) fc

ex5 :: IO ()
ex5 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/functions2.z"
  traverse_ (putStrLn <=< i) fc

ex6 :: IO ()
ex6 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/lazy3.z"
  traverse_ (putStrLn <=< i) fc

ex7 ::  IO ()
ex7 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/fibo.z"
  traverse_ (putStrLn <=< i) fc

ex8 ::  IO ()
ex8 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/subtyped.z"
  traverse_ (putStrLn <=< i) fc

ex9 ::  IO ()
ex9 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/tuples.z"
  traverse_ (putStrLn <=< i) fc

ex10 ::  IO ()
ex10 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/reset.z"
  traverse_ (putStrLn <=< i) fc

ex11 ::  IO ()
ex11 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/random.z"
  traverse_ (putStrLn <=< i) fc

ex12 ::  IO ()
ex12 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/fix.z"
  traverse_ (putStrLn <=< i) fc

ex13 ::  IO ()
ex13 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/bad_redeclarations.z"
  traverse_ (putStrLn <=< i) fc

ex14 ::  IO ()
ex14 = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/functions_with_return.z"
  traverse_ (putStrLn <=< i) fc



nm :: IO ()
nm = do
  i  <- buildUniversalInterpreter
  fc <- lines <$> readFile "./programs/unsugared/custom.z"
  traverse_ (putStrLn <=< i) fc
