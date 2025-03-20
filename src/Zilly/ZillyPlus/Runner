{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ImpredicativeTypes         #-}
module Zilly.Classic.Runner where

import Zilly.RValue
import Zilly.Types
import Zilly.Upcast
import Zilly.ADT.Expression
import Zilly.ADT.Action
import Zilly.Classic.Expression
import Zilly.Classic.Action
import Zilly.Classic.TypeCheck
import Zilly.Classic.Interpreter
import Utilities.ShowM
import Utilities.TypedMap
import Utilities.Codes
import Parser.Classic.ZillyParser qualified as P
import Parser.ParserZ
import Control.Monad.Reader
import Text.Parsec
import Data.Functor.Identity
import Control.Concurrent
import Control.Monad ((>=>))
import Data.Functor (void)
import Data.Map (Map)
import Data.Map qualified as M
data GammaEnv = GammaEnv
  { typingEnv :: Map Symbol Types 
  , valueStore :: TypeRepMap ExprTag
  }

data Err 
    = PErr ParseError 
    | TCErr ErrorLog

instance Show Err where
  show (PErr e)  = "Parser Error!\n" <> show e
  show (TCErr e) = "Typing Error!\n" <> concatMap (\x -> show x <> "\n\n") e

parseAndTypecheck :: FilePath -> IO (Either Err [A ActionTag '()])
parseAndTypecheck fp = P.parseFile' fp >>= \case
  Left e  -> pure $ Left (PErr e)
  Right as -> case typeCheckProgram' M.empty as of
    (_,Nothing,elog) -> pure $ Left (TCErr elog)
    (_,Just as',[])  -> pure $ Right as'
    (_,_,elog)       -> pure $ Left (TCErr elog)

parseAndTypecheck' :: FilePath -> IO ()
parseAndTypecheck' fp = parseAndTypecheck fp >>= \case
  Left e -> putStrLn $ show e
  Right as -> traverse showM as >>= putStrLn . unlines

parseAndRun :: FilePath -> IO (Either Err [A ActionTag '()])
parseAndRun fp = parseAndTypecheck fp >>= \case
  e@(Left _)  -> pure  e
  Right as -> Right . snd <$> runReaderT (runTI  (execProgram empty as )) empty


parseAndRun' :: FilePath -> IO ()
parseAndRun' fp = parseAndRun fp >>= \case
  Left e -> putStrLn $ show e
  Right as -> traverse showM as >>= putStrLn . unlines

parseAndResponse :: (Monad m) => GammaEnv-> Symbol -> IO ([Some (ServerResponse m)], GammaEnv)
parseAndResponse env s =  case P.parsePacket s of
  (Left e) -> pure ([MkSome $ ERRORR $ show  (PErr e)],env)
  (Right (Packet c s t (Payload p) eot)) -> case typeCheckProgram' (typingEnv env) p of
    (tEnv',_,elog@(_:_)) -> pure ([MkSome $ ERRORR $ show (TCErr elog)],env{ typingEnv = tEnv' })
    (tEnv',Nothing,elog) -> pure ([MkSome $ ERRORR $ show (TCErr elog)],env{ typingEnv = tEnv'})
    (tEnv',Just as,_)  -> do
      (vs',as') <- runReaderT (runTI  (execProgram (valueStore env) as )) (valueStore env)
      pure (MkSome . ACKR <$> as',GammaEnv{typingEnv=tEnv',valueStore=vs'})

parseAndResponse' :: GammaEnv -> Symbol -> IO ([Symbol],GammaEnv)
parseAndResponse' env s = do
  (rs,env') <- parseAndResponse @Identity env s 
  let 
    f :: [Some (ServerResponse Identity)] -> [String]
    f = \case
        [] -> []
        (MkSome (ACKR a):s) -> runIdentity (showM a) : f s
        (MkSome (ERRORR e):s) -> e : f s
  pure (f rs,env')

buildInterpreter ::  IO (Symbol -> IO [Symbol])
buildInterpreter = do
  mv  <- newMVar $ GammaEnv{typingEnv=M.empty,valueStore=empty @ExprTag}
  pure $ \s -> do
    env <- readMVar mv
    (results,newEnv) <- parseAndResponse' env s
    void $ swapMVar mv newEnv
    putStr "old env scopes: "
    print $ M.keys $ typingEnv env
    putStr "newEnv scopes: "
    print $ M.keys $ typingEnv newEnv
    pure results

buildInterpreter' ::  IO (Symbol -> IO Symbol)
buildInterpreter' = (fmap . fmap) unlines <$> buildInterpreter

example :: IO ()
example = do
  f <- buildInterpreter'
  f "5[5]\tZ x := 5;\EOT" >>= putStrLn
  f "5[5]\tprint(2 - 2);\EOT" >>= putStrLn
  f "5[5]\tprint(x);\EOT" >>= putStrLn
