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
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Zilly.Unsugared.Runner where

import Zilly.Unsugared.ADT.TypeCheck
import Zilly.Unsugared.ADT.Action
import Zilly.Unsugared.ADT.Expression
import Zilly.Unsugared.Newtypes
import Zilly.Unsugared.Environment.TypedMap
import Zilly.Unsugared.Parser qualified as P
import Zilly.Unsugared.Effects.CC

import Data.Map.Strict (Map)
import Data.Map qualified as M
import Control.Monad.Reader
import Text.Parsec
import Data.Functor.Identity
import Control.Concurrent
import Data.Functor (void)
import Control.Monad ((<=<))
import Data.Foldable (traverse_)
import System.IO.Error
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Applicative (Alternative)
import Debug.Trace (trace)
import Control.Monad.Random
import Control.Monad.State
import Data.Default

data GammaEnv m = GammaEnv
  { typingEnv :: TypeCheckEnv m
  , valueStore :: TypeRepMap (E m)
  }

iMap :: Effects m => IO (GammaEnv m)
iMap = do
  subV   <- newMVar $ subStd
  ltV'    <- newMVar $ ltStd'
  randV  <- newMVar $ randomStd

  pure $ GammaEnv
    { typingEnv = TCE
        { getGamma= M.fromList $ mappend [("random", Z :-> Z)] $ mkBinTypeOp <$>
            [ "sub"
            , "lt"
            ]
        , getCValues = M.fromList $
            [ ("sub",MkSomeExpression minusStd)
            , ("lt",MkSomeExpression ltStd')
            , ("random",MkSomeExpression randomStd)
            ]
        , expectedType= Nothing
        }
    , valueStore = TypeRepMap . M.fromList $
      [ mkStoreFun "sub" subV
      , mkStoreFun "lt" ltV'
      , ("random", MkAny randV)
      ]

    }
  where
    binType = Z :-> Z :-> Z
    mkBinTypeOp x = (x, binType)

    mkStoreFun x y = (x,MkAny y)

instance (Effects m) => Default (m (TypeRepMap (E m))) where
  def = valueStore <$> liftIO iMap

instance (Effects m) => Default (m (TypeCheckEnv m)) where
  def = typingEnv <$> liftIO iMap

newtype ErrorLog' a = ErrorLog [a]
  deriving newtype (Semigroup, Monoid,Functor,Applicative)

instance Show (ErrorLog' (P.BookeepInfo, TypeCheckError)) where
  show (ErrorLog es) = concatMap (\x -> showError x <> "\n\n") es
    where
      showError :: (P.BookeepInfo, TypeCheckError) -> String
      showError (P.tokenPos -> sp, tce) = concat
        [ "At line: "
        , show . sourceLine $ sp
        , " column: "
        , show . sourceColumn $ sp
        , ". "
        , showTypeCheckError tce
        ]
      showTypeCheckError :: TypeCheckError -> String
      showTypeCheckError (NonImplementedFeature f) = "Non implemented feature: " <> f
      showTypeCheckError (CustomError' ce) = ce
      showTypeCheckError (TypeMismatch' (ExpectedType e) (ActualType t)) = concat
        [ "Type Mismatch. "
        , "Expected type: " <> show e
        , ", But got instead: " <> show t
        ]
      showTypeCheckError (FromGammaError' (TypeMismatch s (ExpectedType e) (ActualType t))) = concat
        [ "Variable type Mismatch: " <> show s
        , ". Expected type: " <> show e
        , ", But got instead: " <> show t
        ]
      showTypeCheckError (FromGammaError' (VariableNotDefined s))
        = "Variable not defined: " <> show s
      showTypeCheckError (FromGammaError' (VariableAlreadyDeclared s))
        = "Trying to declare an already existing variable: " <> show s
      showTypeCheckError (FromGammaError' (VariableNotInitialized s))
        = "Trying to use a variable that hasnt been initialized: " <> show s



type ErrorLog = ErrorLog' (P.BookeepInfo,TypeCheckError)
data Err
    = PErr ParseError
    | TCErr ErrorLog

data EvalEnvSt = EvalEnvSt
  { randomSeed :: !Float
  , currentCC  :: !Int
  }

initialEvalEnvSt :: EvalEnvSt
initialEvalEnvSt = EvalEnvSt
  { randomSeed = 0.3141592653589793238462643383279
  , currentCC = 0
  }

newtype EvalEnv a = EvalEnv { runEvalEnv' ::
  CCStateT
    (RandomT
      (StateT EvalEnvSt
        (ReaderT (TypeRepMap (E EvalEnv)) IO
        )
      )
    )
  a}
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , Alternative
    , MonadFail
    , MonadIO
    , MonadReader (TypeRepMap (E EvalEnv))
    )

instance MonadRandom EvalEnv where
  randInt n = EvalEnv . lift $ randInt n

instance MonadCC EvalEnv where
  getCC = EvalEnv getCC
  cycleCC = EvalEnv cycleCC

runEvalEnv :: EvalEnvSt -> TypeRepMap (E EvalEnv) -> EvalEnv a -> IO (a,EvalEnvSt)
runEvalEnv st env (EvalEnv f)
  =  flip runReaderT env
  $ flip runStateT st
  $ do
    ((a,newCC),seed) <- runRandomIO (randomSeed st)
      $ runCCStateT (currentCC st)
      $  f
    _ <- modify $ \st' -> st'{randomSeed=seed,currentCC=newCC}
    pure a

instance Show Err where
  show (PErr e)  = "Parser Error!\n" <> show e
  show (TCErr e) = "Typing Error!\n" <> show e

typeCheckProgram :: forall m. Effects m => P.A1 P.ParsingStage ->  TypeCheckEnv m -> m ( [A m],ErrorLog, TypeCheckEnv m)
typeCheckProgram a env = runWriterT (flip runReaderT env $ typeCheckA1 @m a) >>= \case
  ((as,env'),logs) -> pure (as,logs,env')

parseAndTypecheck :: FilePath -> IO (Either Err [A EvalEnv], EvalEnvSt)
parseAndTypecheck fp = P.parseFile' fp >>= \case
  Left e  -> pure (Left (PErr e), initialEvalEnvSt)
  Right as -> (runEvalEnv initialEvalEnvSt empty ) (typeCheckProgram @EvalEnv as (TCE M.empty M.empty Nothing)) >>= \case
    ((_,ErrorLog elog@(_:_),_),st) -> pure (Left (TCErr $ ErrorLog elog),st)
    ((as',_,_),st)  -> pure (Right as',st)

parseAndTypecheck' :: FilePath -> IO ()
parseAndTypecheck' fp = fst <$> parseAndTypecheck fp >>= \case
  Left e -> print e
  Right as -> traverse_ print as


parseAndRun :: FilePath -> IO (Either String [A EvalEnv],EvalEnvSt)
parseAndRun fp = parseAndTypecheck fp >>= \case
  (e@(Left _),st)  -> pure (Left . show $ e,st)
  (Right as,st) -> (runEvalEnv st empty) $ evalProgram as >>= \case
    Left errs -> pure . Left . showRuntimeError $ errs
    Right (_,as') -> pure . Right $ as'


parseAndRun' :: FilePath -> IO ()
parseAndRun' fp = fst <$> parseAndRun fp >>= \case
  Left e -> putStrLn e
  Right as -> traverse_ print as

parseAndResponse :: EvalEnvSt -> GammaEnv EvalEnv -> String -> IO (String, GammaEnv EvalEnv, EvalEnvSt)
parseAndResponse st env s = case P.parseAction' s of
  Left e -> pure ("Error: parsing error, " <> show e, env,st)
  Right a
    -> (runEvalEnv st (valueStore env) ) (typeCheckProgram @EvalEnv a (typingEnv env)) >>= \case
      ((_,ErrorLog elog@(_:_),tEnv'),st') -> pure ("Error: " <> show (ErrorLog elog),env{typingEnv=tEnv'},st')
      ((as,_,tEnv'),st') -> runEvalEnv st' (valueStore env) (evalProgram as) >>= \case
        (Left err,st'') -> pure ("Error: runtime error, " <> showRuntimeError err,env{typingEnv=tEnv'},st'')
        (Right (newStore,as'),st'') -> do
          -- aux <- sequence [ (\(MkAny v') -> (\v2 -> k <> " :- " <> show v2) <$> liftIO  (tryReadMVar v')) v  | (k,v) <- (\(TypeRepMap m) -> M.assocs m) newStore]
          -- liftIO $ traverse_ putStrLn aux
          pure
            ( unlines $ uncurry g <$> zip as as'
            , GammaEnv{typingEnv=tEnv',valueStore=newStore}
            , st''
            )
  where
    g :: A m -> A m -> String
    g (Print e0) e1 = "OK: " <> show e0 <> " ==> "  <> show e1
    g l r = "ACK: "  <> show r

buildInterpreter ::  IO (String -> IO String)
buildInterpreter = do
  mv  <- iMap >>= newMVar
  mst <- newMVar initialEvalEnvSt
  pure $ \s -> do
    env <- readMVar mv
    st  <- readMVar mst
    catchIOError
      ( do
        (results,newEnv,st') <- parseAndResponse st env s
        void $ swapMVar mv newEnv
        void $ swapMVar mst st'
        pure results
      )
      (\e -> pure ("Error: " <> show e))


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

ex6 :: IO ()
ex6 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/lazy3.z"
  traverse_ (putStrLn <=< i) fc

ex7 ::  IO ()
ex7 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/fibo.z"
  traverse_ (putStrLn <=< i) fc

ex8 ::  IO ()
ex8 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/subtyped.z"
  traverse_ (putStrLn <=< i) fc

ex9 ::  IO ()
ex9 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/tuples.z"
  traverse_ (putStrLn <=< i) fc

ex10 ::  IO ()
ex10 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/reset.z"
  traverse_ (putStrLn <=< i) fc

ex11 ::  IO ()
ex11 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/random.z"
  traverse_ (putStrLn <=< i) fc

ex12 ::  IO ()
ex12 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/fix.z"
  traverse_ (putStrLn <=< i) fc



nm :: IO ()
nm = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/custom.z"
  traverse_ (putStrLn <=< i) fc
