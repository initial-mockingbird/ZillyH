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
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE QuantifiedConstraints      #-}
module Zilly.Classic.Runner where

import Zilly.Types
import Zilly.ADT.Action
import Zilly.Classic.Expression
import Zilly.Classic.Action
import Zilly.Classic.TypeCheck2
import Zilly.Classic.Interpreter
import Utilities.ShowM
import Utilities.TypedMap
import Parser.ClassicPlus.ZillyPlusParser qualified as P
import Control.Monad.Reader
import Text.Parsec
import Data.Functor.Identity
import Control.Concurrent
import Data.Functor (void)
import Data.Map (Map)
import Data.Map qualified as M
import Zilly.ADT.Expression (E)
import Control.Monad ((<=<))
import Data.Foldable (traverse_)
import System.IO.Error 

data GammaEnv = GammaEnv
  { typingEnv :: Map Symbol Types 
  , valueStore :: TypeRepMap ExprTag
  }

iMap :: IO GammaEnv 
iMap = do 
  minusV <- newMVar $ minusStd
  plusV  <- newMVar $ plusStd
  ltV    <- newMVar $ ltStd
  eqV    <- newMVar $ eqStd
  gtV    <- newMVar $ gtStd
  orV    <- newMVar $ orStd 
  notV   <- newMVar $ notStd
  andV   <- newMVar $ andStd
  ltEqV  <- newMVar $ ltEqStd
  gtEqV  <- newMVar $ gtEqStd
  nEqV   <- newMVar $ nEqStd
  absV   <- newMVar $ absStd
  chsV   <- newMVar $ chsStd 
  _mltV  <- newMVar $ _mltStd
  _mulV  <- newMVar $ _mulStd 
  mulV   <- newMVar $ mulStd

  pure $ GammaEnv 
    { typingEnv = M.fromList $ mappend [("not", Value Z ~~> Value Z)] $ mkBinTypeOp <$> 
      [ "minus"
      , "plus"
      , "lt"
      , "eq"
      , "gt"
      , "or"
      , "and"
      , "lteq"
      , "gteq"
      , "neq"
      , "abs"
      , "chs"
      , "_mlt"
      , "_mul"
      , "mul"
      ]
    , valueStore = TypeRepMap . M.fromList $ 
      [ mkStoreFun "minus" minusV
      , mkStoreFun "plus" plusV
      , mkStoreFun "lt" ltV 
      , mkStoreFun "eq" eqV 
      , mkStoreFun "gt" gtV 
      , mkStoreFun "or" orV 
      , mkStoreFun "and" andV 
      , mkStoreFun "lteq" ltEqV 
      , mkStoreFun "gteq" gtEqV
      , mkStoreFun "neq" nEqV 
      , mkStoreFun "_mlt" _mltV 
      , mkStoreFun "_mul" _mulV 
      , mkStoreFun "mul"  mulV
      , ("not",MkAny notV)
      , ("abs",MkAny absV)
      , ("chs",MkAny chsV)
      ]

    }
  where 
    binType = Value Z ~~> Value Z ~~> Value Z
    mkBinTypeOp x = (x, binType)

    mkStoreFun x y = (x,MkAny y)

    

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
  Left e -> print e
  Right as -> traverse showM as >>= putStrLn . unlines

parseAndRun :: FilePath -> IO (Either Err [A ActionTag '()])
parseAndRun fp = parseAndTypecheck fp >>= \case
  e@(Left _)  -> pure  e
  Right as -> Right . snd <$> runReaderT (runTI  (execProgram empty as )) empty


parseAndRun' :: FilePath -> IO ()
parseAndRun' fp = parseAndRun fp >>= \case
  Left e -> print e
  Right as -> traverse showM as >>= putStrLn . unlines


parseAndResponse :: GammaEnv-> Symbol -> IO (Symbol, GammaEnv)
parseAndResponse env s =  case P.parseAction' s of
  (Left e) -> pure ("Error: parsing error,  " <> show e,env)
  (Right a) -> case typeCheckProgram' (typingEnv env) a of
    (tEnv',_,elog@(_:_)) -> pure (unlines ["Error: " <> show e | e <- elog],env{ typingEnv = tEnv' })
    (tEnv',Nothing,elog) -> pure (unlines ["Error: " <> show e | e <- elog],env{ typingEnv = tEnv'})
    (tEnv',Just as,_)  -> do
      (vs',as') <- runReaderT (runTI  (execProgram (valueStore env) as )) (valueStore env)
      pure (unlines $ uncurry g <$> zip as as',GammaEnv{typingEnv=tEnv',valueStore=vs'})
  where 
    g :: forall x0 x1. A ActionTag x0 -> A ActionTag x1 -> String
    g (Print @_ @a l) r  = "OK: "  <> (runIdentity . showM @_ @(E ExprTag a) ) l <> " ==> " <> (runIdentity . showM @_ @(A ActionTag x1 ) ) r
    g (OfExpr @_ @a l) r = "OK: "  <> (runIdentity . showM @_ @(E ExprTag a) ) l <> " ==> " <> (runIdentity . showM @_ @(A ActionTag x1 ) ) r
    g _ r          = "ACK: " <> (runIdentity . showM ) r <> ";"

buildInterpreter ::  IO (Symbol -> IO Symbol)
buildInterpreter = do
  mv  <- iMap >>= newMVar
  pure $ \s -> do
    env <- readMVar mv
    catchIOError
      ( do
        (results,newEnv) <- parseAndResponse env s
        void $ swapMVar mv newEnv
        pure results
      ) 
      (\e -> pure ("Error: " <> show e))

buildInterpreter' = buildInterpreter



ex0 :: IO ()
ex0 = do 
  i  <- buildInterpreter 
  fc <- lines <$> readFile "./programs/equality.z"
  traverse_ (putStrLn <=< i) fc

ex1 :: IO ()
ex1 = do 
  i  <- buildInterpreter 
  fc <- lines <$> readFile "./programs/comparison.z"
  traverse_ (putStrLn <=< i) fc

ex2 :: IO ()
ex2 = do 
  i  <- buildInterpreter 
  fc <- lines <$> readFile "./programs/lazy1.z"
  traverse_ (putStrLn <=< i) fc

ex3 :: IO ()
ex3 = do 
  i  <- buildInterpreter 
  fc <- lines <$> readFile "./programs/lazy2.z"
  traverse_ (putStrLn <=< i) fc

ex4 :: IO ()
ex4 = do 
  i  <- buildInterpreter 
  fc <- lines <$> readFile "./programs/functions.z"
  traverse_ (putStrLn <=< i) fc

ex5 :: IO ()
ex5 = do 
  i  <- buildInterpreter 
  fc <- lines <$> readFile "./programs/functions2.z"
  traverse_ (putStrLn <=< i) fc


