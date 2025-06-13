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
{-# LANGUAGE TupleSections #-}

module Zilly.Classic.Runner where

import Zilly.Classic.ADT.TypeCheck
import Zilly.Unsugared.ADT.Action
import Zilly.Unsugared.ADT.Expression
import Zilly.Unsugared.Newtypes
import Zilly.Unsugared.Environment.TypedMap
import Zilly.Unsugared.Environment.TypedMap qualified as TM
import Zilly.Classic.Parser qualified as P
import Zilly.Unsugared.Effects.CC

import Data.Map.Strict (Map)
import Data.Map qualified as M
import Control.Monad.Reader
import Text.Parsec
import Data.Functor.Identity
import Control.Concurrent
import Data.Functor (void)
import Control.Monad ((<=<), forM_)
import Data.Foldable (traverse_)
import System.IO.Error
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Applicative (Alternative)
import Debug.Trace (trace)
import Control.Monad.Random
import Control.Monad.State
import Data.Default
import Control.Monad.Error.Class
import Control.Exception
import Data.Typeable
import Zilly.Unsugared.Effects.Block
import Data.Set qualified as S
import Prelude.Singletons
import Zilly.Unsugared.Newtypes
import Data.Foldable (foldlM)

data GammaEnv m = GammaEnv
  { typingEnv :: TypeCheckEnv m
  , valueStore :: TypeRepMap (E m)
  }

iMap :: EnvEffs m => IO (GammaEnv m)
iMap = do
  subV   <- newMVar $ subStd
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
  randV  <- newMVar $ randomStd

  pure $ GammaEnv
    { typingEnv = TCE
        { getGamma= M.fromList $ mappend [("not", Z :-> Z),("chs", Z :-> Z), ("random", Z :-> Z)] $ mkBinTypeOp <$>
            [ "sub"
            , "minus"
            , "plus"
            , "lt"
            , "eq"
            , "gt"
            , "or"
            , "and"
            , "le"
            , "ge"
            , "ne"
            , "abs"
            , "_mlt"
            , "_mul"
            , "mul"
            ]
        , getCValues = M.fromList $
            [ ("sub",MkSomeExpression subStd)
            , ("minus",MkSomeExpression minusStd)
            , ("plus",MkSomeExpression plusStd)
            , ("lt",MkSomeExpression ltStd)
            , ("eq",MkSomeExpression eqStd)
            , ("gt",MkSomeExpression gtStd)
            , ("or",MkSomeExpression orStd)
            , ("and",MkSomeExpression andStd)
            , ("le",MkSomeExpression ltEqStd)
            , ("ge",MkSomeExpression gtEqStd)
            , ("ne",MkSomeExpression nEqStd)
            , ("_mlt",MkSomeExpression _mltStd)
            , ("_mul",MkSomeExpression _mulStd)
            , ("mul",MkSomeExpression mulStd)
            , ("not",MkSomeExpression notStd)
            , ("abs",MkSomeExpression absStd)
            , ("chs",MkSomeExpression chsStd)
            , ("random",MkSomeExpression randomStd)
            ]
        , expectedType= Nothing
        }
    , valueStore = TypeRepMap . M.fromList $
      [ mkStoreFun "sub" subV
      , mkStoreFun "minus" minusV
      , mkStoreFun "plus" plusV
      , mkStoreFun "lt" ltV
      , mkStoreFun "eq" eqV
      , mkStoreFun "gt" gtV
      , mkStoreFun "or" orV
      , mkStoreFun "and" andV
      , mkStoreFun "le" ltEqV
      , mkStoreFun "ge" gtEqV
      , mkStoreFun "ne" nEqV
      , mkStoreFun "_mlt" _mltV
      , mkStoreFun "_mul" _mulV
      , mkStoreFun "mul"  mulV
      , ("not",MkAny notV)
      , ("abs",MkAny absV)
      , ("chs",MkAny chsV)
      , ("random", MkAny randV)
      ]

    }
  where
    binType = Z :-> Z :-> Z
    mkBinTypeOp x = (x, binType)

    mkStoreFun x y = (x,MkAny y)

instance (EnvEffs m) => Default (m (TypeRepMap (E m))) where
  def = valueStore <$> liftIO iMap

instance (EnvEffs m) => Default (m (TypeCheckEnv m)) where
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
  { randomSeed  :: !Float
  , currentCC   :: !Int
  , currentQ    :: !Int
  , gammaEnv    :: GammaEnv EvalEnv
  , blockErrors :: Block (AError (P.A0 P.ParsingStage))
  , queuedAs    :: Block (P.A0 P.ParsingStage)
  , logs        :: [String]
  }

initialEvalEnvSt :: IO EvalEnvSt
initialEvalEnvSt = iMap >>= \imap -> pure $  EvalEnvSt
  { randomSeed  = 0.3141592653589793238462643383279
  , currentCC   = 0
  , currentQ    = 0
  , gammaEnv    = imap
  , blockErrors = []
  , queuedAs    = []
  , logs        = []
  }


logMsg :: String -> EvalEnv ()
logMsg e = modify $ \st -> st{logs = e : logs st}

newtype EvalEnv a = EvalEnv { runEvalEnv' ::
  StateT EvalEnvSt IO
  a}
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , Alternative
    , MonadIO
    , MonadState EvalEnvSt
    )

instance MonadRandom EvalEnv where
  randInt n = do
    seed <- gets randomSeed
    (r,nextSeed) <- liftIO $ runRandomIO seed $ randInt n
    modify $ \st -> st{randomSeed=nextSeed}
    pure r

instance MonadCC EvalEnv where
  getCC = gets currentCC
  cycleCC = modify $ \st -> st{currentCC = currentCC st + 1}

instance ReportBlock EvalEnv (P.A0 P.ParsingStage) where
  reportError e = modify $ \st -> st{blockErrors = e : blockErrors st}

instance AccAction EvalEnv (P.A0 P.ParsingStage) where
  queueAction a = modify $ \st -> st{queuedAs = a : queuedAs st}
  getAcc = gets queuedAs <* modify (\st -> st{queuedAs = []})

instance CCActions EvalEnv where
  getQ = gets currentQ
  putQ q = modify $ \st -> st{currentQ = q}

instance EnvOperations EvalEnv (TypeCheckEnv EvalEnv) where
  type EnvElem (TypeCheckEnv EvalEnv) = P.A0 P.ParsingStage
  declare (P.Decl t a _ _) = case S.toList $ getVar a of
    [] -> throwError "Cannot declare an empty variable"
    (_:_:_) -> throwError "Cannot declare multiple variables at once"
    [v] -> do
      gamma <- gets gammaEnv
      let tEnv = typingEnv gamma
      let vStr = valueStore gamma
      let newGamma = TCE
            { getGamma = M.insert v t (getGamma tEnv)
            , getCValues = getCValues tEnv
            , expectedType = Just t
            }
      newVStr <- case toSing t of
        SomeSing @_ @t' t'
          -> withSingI t'
          $ withSingIFtype @t'
          $ TM.declareFresh @(Ftype t') v
          $ vStr
      let newEnv = gamma{typingEnv = newGamma, valueStore = newVStr}

      modify $ \st -> st{gammaEnv = newEnv}
      pure newGamma
  declare a = throwError $ "Action: " <> show a <> " is not a definition"
  getEnv = gets (typingEnv . gammaEnv)
  inScope = gets $ S.fromList . M.keys . getGamma . typingEnv . gammaEnv
  withEnv env f = do
    oldEnv <- gets gammaEnv
    modify $ \st -> st{gammaEnv = oldEnv{typingEnv = env}}
    result <- f
    modify $ \st -> st{gammaEnv = oldEnv}
    pure result

type instance EvalMonad (E EvalEnv) = EvalEnv
instance HasTypeRepMap (E EvalEnv) where

  getEnv = gets (valueStore . gammaEnv)
  withEnv env ma = do
    oldEnv <- gets gammaEnv
    modify $ \st -> st{gammaEnv = oldEnv{valueStore = env}}
    result <- ma
    modify $ \st -> st{gammaEnv = oldEnv}
    pure result



newtype EvalEnvError = EvalEnvError String

instance Show EvalEnvError where
  show (EvalEnvError e) = "Error: " <> e

instance Exception EvalEnvError where
  displayException (EvalEnvError e) = "EvalEnv Error: " <> e
  fromException (SomeException @e e) | Just Refl <- eqT @EvalEnvError @e = Just e
  fromException _ = Nothing
  toException = SomeException

instance MonadError String EvalEnv where
  throwError e = liftIO $ throwIO (EvalEnvError e)
  catchError (EvalEnv f) h = EvalEnv $
    catchError f $ \e -> case fromException @EvalEnvError $ toException e of
      Just (EvalEnvError e') -> runEvalEnv' $ h e'
      Nothing -> liftIO $ throwError e

runEvalEnv :: EvalEnvSt ->  EvalEnv a -> IO (a,EvalEnvSt)
runEvalEnv st  (EvalEnv f) = runStateT f st


lex :: String -> EvalEnv (P.A0 P.ParsingStage)
lex s = case P.parseSingleAction s of
  Left e -> throwError $ "Lexing error: " <> show e
  Right a -> pure a

r1 :: P.A0 P.ParsingStage -> EvalEnv ([P.A0 P.ParsingStage], Maybe (P.A0 P.ParsingStage))
r1 a@(P.Decl _ (getVar -> vs) _ _) =  do
  scoped <- inScope @EvalEnv @(TypeCheckEnv EvalEnv)
  case null $ S.difference vs scoped of
    False ->  queueAction a >> pure ([], Nothing)
    _   -> do
      throwError $ "Variable redeclaration: " <> show vs

r1 a = do
  gamma <- gets gammaEnv
  (newEnv,pending) <- processPending @EvalEnv @(P.A0 P.ParsingStage) @(TypeCheckEnv EvalEnv)
    $ \a' -> (,a') <$> gets (typingEnv . gammaEnv)

  let newGamma = gamma{typingEnv = newEnv}
  modify $ \st -> st{gammaEnv = newGamma}
  pure (pending, Just a)


tc1 :: [P.A0 P.ParsingStage] -> EvalEnv ([A EvalEnv], TypeCheckEnv EvalEnv)
tc1 xs = do
  env <- gets (typingEnv . gammaEnv)
  ((as,env'),errs) <- runWriterT $ runReaderT (xs' env) env
  forM_ errs $ \(P.BI pos _, tce) -> do
    logMsg
      $ "Error at "
      <> show (sourceLine pos)
      <> ":"
      <> show (sourceColumn pos)
      <> ", "
      <> showTypeCheckError tce
  pure (as, env')
  where
  xs' :: TypeCheckEnv EvalEnv
    -> ReaderT (TypeCheckEnv EvalEnv)
        ( WriterT [(P.BookeepInfo, TypeCheckError)]
          EvalEnv
        )
        ([A EvalEnv], TypeCheckEnv EvalEnv)
  xs' env = (\ acc as f -> foldlM f acc as) ([],env) xs $ \ (acc,env') a -> do
    (a',env'') <- local (const env') $ typeCheckA0 a
    pure (acc <> [a'], env'')

evalAs :: [A EvalEnv] -> EvalEnv ([A EvalEnv], TypeRepMap (E EvalEnv))
evalAs as = do
  as' <- (\acc xs f -> foldlM f acc xs) [] as $ \acc a -> do
    (store',a') <- evalA' a
    modify $ \st' -> st'{gammaEnv = (gammaEnv st'){valueStore = store'}}
    pure (acc <> [a'])
  st' <- gets (valueStore . gammaEnv)
  pure (as', st')

process :: String -> EvalEnv ()
process s = do
  a <- Zilly.Classic.Runner.lex s
  (pending,mnew) <- r1 a
  case mnew of
    Nothing -> logMsg $ "ACK: " <> show a
    Just a' -> do
      (tcs,tcEnv) <- tc1 pending
      modify $ \st -> st{gammaEnv = (gammaEnv st){typingEnv = tcEnv}}
      (results,store) <- evalAs tcs
      modify $ \st -> st{gammaEnv = (gammaEnv st){valueStore = store}}
      forM_ results $ \r -> logMsg $ "ASY: " <> show r
      (tca, tcEnv') <- tc1 [a']
      modify $ \st -> st{gammaEnv = (gammaEnv st){typingEnv = tcEnv'}}
      (result,store') <- evalAs tca
      modify $ \st -> st{gammaEnv = (gammaEnv st){valueStore = store'}}
      forM_ result $ \r -> case r of
        Print e -> logMsg $ "OK: " <> show e
        _       -> logMsg $ "ACK: " <> show r

processAndResponse :: String -> EvalEnv [String]
processAndResponse s = do
  process s `catchError` \e -> do
    logMsg $ "Error: " <> e
  logs' <- gets logs
  modify $ \st -> st{logs = []}
  blockErrs <- gets blockErrors
  modify $ \st -> st{blockErrors = []}
  let blockErrs' = flip fmap blockErrs $ \case
        Deceased a -> "Error: Deceased variable " <> show a
        NonStaticallyConstructive a -> "Error: Non statically constructivie variable " <> show a
        RuntimeError a -> "Error: Runtime error " <> show a
  pure $ blockErrs' <> logs'



buildInterpreter ::  IO (String -> IO String)
buildInterpreter = do
  mst <- initialEvalEnvSt >>= newMVar
  pure $ \s -> do
    st <- readMVar mst
    catchIOError
      ( do
        (results, newMst) <- runEvalEnv st $ processAndResponse s
        void $ swapMVar mst newMst
        pure $ unlines  results
      )
      (\e -> pure ("Error: " <> show e))

buildInterpreter' = buildInterpreter


-- instance Show Err where
--   show (PErr e)  = "Parser Error!\n" <> show e
--   show (TCErr e) = "Typing Error!\n" <> show e
--
-- typeCheckProgram :: forall m. Effects m => P.A1 P.ParsingStage ->  TypeCheckEnv m -> m ( [A m],ErrorLog, TypeCheckEnv m)
-- typeCheckProgram a env = runWriterT (flip runReaderT env $ typeCheckA1 @m a) >>= \case
--   ((as,env'),logs) -> pure (as,logs,env')
--
-- parseAndTypecheck :: FilePath -> IO (Either Err [A EvalEnv], EvalEnvSt)
-- parseAndTypecheck fp = P.parseFile' fp >>= \case
--   Left e  -> pure (Left (PErr e), initialEvalEnvSt)
--   Right as -> (runEvalEnv initialEvalEnvSt empty ) (typeCheckProgram @EvalEnv as (TCE M.empty M.empty Nothing)) >>= \case
--     ((_,ErrorLog elog@(_:_),_),st) -> pure (Left (TCErr $ ErrorLog elog),st)
--     ((as',_,_),st)  -> pure (Right as',st)
--
-- parseAndTypecheck' :: FilePath -> IO ()
-- parseAndTypecheck' fp = fst <$> parseAndTypecheck fp >>= \case
--   Left e -> print e
--   Right as -> traverse_ print as
--
--
-- parseAndRun :: FilePath -> IO (Either String [A EvalEnv],EvalEnvSt)
-- parseAndRun fp = parseAndTypecheck fp >>= \case
--   (e@(Left _),st)  -> pure (Left . show $ e,st)
--   (Right as,st) -> (runEvalEnv st empty) $ evalProgram as >>= \case
--     Left errs -> pure . Left . showRuntimeError $ errs
--     Right (_,as') -> pure . Right $ as'
--
--
-- parseAndRun' :: FilePath -> IO ()
-- parseAndRun' fp = fst <$> parseAndRun fp >>= \case
--   Left e -> putStrLn e
--   Right as -> traverse_ print as
--
-- parseAndResponse :: EvalEnvSt -> GammaEnv EvalEnv -> String -> IO (String, GammaEnv EvalEnv, EvalEnvSt)
-- parseAndResponse st env s = case P.parseAction' s of
--   Left e -> pure ("Error: parsing error, " <> show e, env,st)
--   Right a
--     -> (runEvalEnv st (valueStore env) ) (typeCheckProgram @EvalEnv a (typingEnv env)) >>= \case
--       ((_,ErrorLog elog@(_:_),tEnv'),st') -> pure ("Error: " <> show (ErrorLog elog),env{typingEnv=tEnv'},st')
--       ((as,_,tEnv'),st') -> runEvalEnv st' (valueStore env) (evalProgram as) >>= \case
--         (Left err,st'') -> pure ("Error: runtime error, " <> showRuntimeError err,env{typingEnv=tEnv'},st'')
--         (Right (newStore,as'),st'') -> do
--           -- aux <- sequence [ (\(MkAny v') -> (\v2 -> k <> " :- " <> show v2) <$> liftIO  (tryReadMVar v')) v  | (k,v) <- (\(TypeRepMap m) -> M.assocs m) newStore]
--           -- liftIO $ traverse_ putStrLn aux
--           pure
--             ( unlines $ uncurry g <$> zip as as'
--             , GammaEnv{typingEnv=tEnv',valueStore=newStore}
--             , st''
--             )
--   where
--     g :: A m -> A m -> String
--     g (Print e0) e1 = "OK: " <> show e0 <> " ==> " <> show e1
--     g l r = "ACK: " <> show r
--
-- buildInterpreter ::  IO (String -> IO String)
-- buildInterpreter = do
--   mv  <- iMap >>= newMVar
--   mst <- newMVar initialEvalEnvSt
--   pure $ \s -> do
--     env <- readMVar mv
--     st  <- readMVar mst
--     catchIOError
--       ( do
--         (results,newEnv,st') <- parseAndResponse st env s
--         void $ swapMVar mv newEnv
--         void $ swapMVar mst st'
--         pure results
--       )
--       (\e -> pure ("Error: " <> show e))
--
-- buildInterpreter' = buildInterpreter
--
ex0 :: IO ()
ex0 = do
  i  <- buildInterpreter
  fc <- lines <$> readFile "./programs/equality.z"
  traverse_ (putStrLn <=< i) fc
--
-- ex1 :: IO ()
-- ex1 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/comparison.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex2 :: IO ()
-- ex2 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/lazy1.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex3 :: IO ()
-- ex3 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/lazy2.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex4 :: IO ()
-- ex4 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/functions.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex5 :: IO ()
-- ex5 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/functions2.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex6 :: IO ()
-- ex6 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/lazy3.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex7 ::  IO ()
-- ex7 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/fibo.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex8 ::  IO ()
-- ex8 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/subtyped.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex9 ::  IO ()
-- ex9 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/tuples.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex10 ::  IO ()
-- ex10 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/reset.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex11 ::  IO ()
-- ex11 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/random.z"
--   traverse_ (putStrLn <=< i) fc
--
-- ex12 ::  IO ()
-- ex12 = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/fix.z"
--   traverse_ (putStrLn <=< i) fc
--
--
--
-- nm :: IO ()
-- nm = do
--   i  <- buildInterpreter
--   fc <- lines <$> readFile "./programs/custom.z"
--   traverse_ (putStrLn <=< i) fc
