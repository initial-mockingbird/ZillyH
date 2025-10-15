{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Zilly.Puzzle.Runner where

import Zilly.Puzzle.Parser qualified as P
import Zilly.Puzzle.Parser (Parser)
import Zilly.Puzzle.Expression.Exports
import Zilly.Puzzle.Action.Exports
import Zilly.Puzzle.Environment.TypedMap hiding (fromList,toList)
import Zilly.Puzzle.Effects.CC
import Zilly.Puzzle.Types.Exports
import Zilly.Puzzle.Effects.Block (CCActions(..))
import Zilly.Puzzle.TypeCheck.Exports

import Control.Monad.Random
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.Except
import Control.Exception
import Data.Typeable
import Control.Applicative
import Data.Default
import Data.Set (Set)
import Data.List (intercalate)
import Zilly.Puzzle.Environment.TypedMap qualified as M
import Data.Set qualified as S
import Control.Concurrent
import Control.Monad
import Text.Parsec hiding((<|>), parse)
import Data.Functor.Identity
import Data.String (IsString(..))
import Data.Functor ((<$), ($>))
import Data.Foldable (traverse_)
import Control.Monad.Except
import Debug.Trace (trace)
import System.Random (randomIO)




-------------------------------
-- Useful Orphans
-------------------------------




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



data PuzzleState = PuzzleState
  { pstIntSeed    :: Int
  , pstDoubleSeed :: Double
  , pstCC         :: Int
  , pstVarDict    :: TypeRepMap (E PRunnerCtx)
  , pstQ          :: Int
  , pstEnabledExtensions :: Set Extensions
  , pstEvalE      :: E PRunnerCtx -> PuzzleM (E PRunnerCtx)
  }
data PuzzleReader = PuzzleReader
  { prExpectedType :: Set Types

  }
type PuzzleWriter = ()

data PRunnerCtx

data PuzzleError = PuzzleError String
  deriving (Typeable)

instance Show PuzzleError where
  show (PuzzleError msg) = "Error: " <> msg

instance Exception PuzzleError where
  toException e   = SomeException e
  fromException (SomeException @e e) | Just Refl <- eqT @PuzzleError @e = Just e
  fromException _ = Nothing

  -- fromException (SomeException e) = cast e
  displayException (PuzzleError msg) = "Error: " <> msg



newtype PuzzleM a = PuzzleM
  { runPuzzle :: (RWST PuzzleReader PuzzleWriter PuzzleState  (ExceptT String IO)) a }
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadIO
    , Alternative
    , MonadReader PuzzleReader
    , MonadWriter PuzzleWriter
    , MonadState PuzzleState
    )

runPuzzleM :: PuzzleState -> PuzzleM a -> IO (Either String (a, PuzzleState))
runPuzzleM initialState (PuzzleM ma) = do
  let initialReader = PuzzleReader S.empty
  fmap (\(a,b,_) -> (a,b)) <$> runExceptT (runRWST ma initialReader initialState)

instance TCMonad PuzzleM where
  getExpectedType = asks prExpectedType
  withExpectedType tempEnv ma = local (\s -> s { prExpectedType = tempEnv }) ma
  validateType bk t = do
    expected <- getExpectedType
    let b = any (`isSuperTypeOf` t)  expected || null expected
    unless b $ throwError
      $ "At: " <> show (P.tokenPos bk)
      <>  ". Type " <> show t
      <> " is not expected in the current context: "
      <> intercalate ", " (map show $ S.toList expected)

instance ExtensionCheckEff PuzzleM where
  validateExtension ext (bk) = do
    enabled <- gets pstEnabledExtensions
    unless (ext `S.member` enabled) $
      throwError $ "At: " <> show (P.tokenPos bk) <>  ". Extension " ++ show ext ++ " is not enabled in the current context."

  getEnabledExtensions = S.toList <$> gets pstEnabledExtensions

instance MonadError String PuzzleM where
  throwError  = PuzzleM . lift . throwError @String @(ExceptT String IO)
  catchError (PuzzleM f) h = PuzzleM $ f `catchError` (runPuzzle . h)

instance MonadRandom PuzzleM where
  randInt ub = floor <$> randFloat (fromIntegral ub)
  randFloat ub = do
    seed <- gets pstDoubleSeed
    let n' = seed * 997 - (fromInteger . floor) (seed * 997)
    modify (\s -> s { pstDoubleSeed = n' })
    pure . max 0 $  ub * n'


instance MonadCC PuzzleM where
  getCC = gets pstCC
  cycleCC = modify (\s -> s { pstCC = pstCC s + 1 })

instance HasLType (E PRunnerCtx) where
  varLType = yieldMetadata

instance HasTypeRepMap (E PRunnerCtx) where
  getEnv = gets pstVarDict
  withEnv tempEnv ma = do
    env <- getEnv
    modify (\s -> s { pstVarDict = tempEnv })  -- Temporarily set new environment
    a <- ma
    modify (\s -> s { pstVarDict = env })  -- Restore original environment
    pure a

instance HasArgType PRunnerCtx LambdaTag where
  type ArgType PRunnerCtx LambdaTag = LambdaCtx PRunnerCtx
  argType = fst

instance HasRetType PRunnerCtx LambdaTag where
  type RetType PRunnerCtx LambdaTag = LambdaCtx PRunnerCtx
  retType = snd

instance HasArgType PRunnerCtx LambdaCTag where
  type ArgType PRunnerCtx LambdaCTag = LambdaCCtx PRunnerCtx
  argType = fst

instance HasRetType PRunnerCtx LambdaCTag where
  type RetType PRunnerCtx LambdaCTag = LambdaCCtx PRunnerCtx
  retType = snd

instance CCActions PuzzleM where
  getQ = gets pstQ
  putQ n = modify (\s -> s { pstQ = n })

type instance EvalMonad (E PRunnerCtx) = PuzzleM
type instance VarMetadata (E PRunnerCtx) = Types
type instance LambdaCtx PRunnerCtx = (Types, Maybe Types)
type instance LambdaCCtx PRunnerCtx = LambdaCtx PRunnerCtx

instance Default (PuzzleM (TypeRepMap (E PRunnerCtx))) where
  def = do
    b <- null <$> getEnabledExtensions
    if b then liftIO imap
    else liftIO imapComplete


imap :: IO (TypeRepMap (E PRunnerCtx))
imap = do
  subV   <- newMVar $ subStd  @PRunnerCtx
  ltV    <- newMVar $ ltStd'  @PRunnerCtx

  pure $ M.fromList
    [ ("sub", subV, Z :-> Z :-> Z)
    , ("lt", ltV, Z :-> Z :-> Z)
    ]



imapComplete :: IO (TypeRepMap (E PRunnerCtx))
imapComplete = do
  uminusV  <- newMVar $ uminusStd @PRunnerCtx
  negateV  <- newMVar $ negateStd @PRunnerCtx
  powV     <- newMVar $ powStd    @PRunnerCtx
  mulV     <- newMVar $ timesStd  @PRunnerCtx
  divV     <- newMVar $ divStd    @PRunnerCtx
  subV     <- newMVar $ subStd    @PRunnerCtx
  minusV   <- newMVar $ minusStd  @PRunnerCtx
  plusV    <- newMVar $ plusStd   @PRunnerCtx
  appendV  <- newMVar $ appendStd @PRunnerCtx
  ltV      <- newMVar $ ltStd     @PRunnerCtx
  leV      <- newMVar $ leStd     @PRunnerCtx
  gtV      <- newMVar $ gtStd     @PRunnerCtx
  geV      <- newMVar $ geStd     @PRunnerCtx
  eqV      <- newMVar $ eqStd     @PRunnerCtx
  neV      <- newMVar $ neStd     @PRunnerCtx
  andV     <- newMVar $ andStd    @PRunnerCtx
  orV      <- newMVar $ orStd     @PRunnerCtx
  eV       <- newMVar $ eStd      @PRunnerCtx

  pure $ M.fromList
    [ ("uminus", uminusV, Z :-> Z)
    , ("negate", negateV, ZBool :-> ZBool)
    , ("pow", powV, Z :-> Z :-> Z)
    , ("mul", mulV, Z :-> Z :-> Z)
    , ("div", divV, Z :-> Z :-> Z)
    , ("sub", subV, Z :-> Z :-> Z)
    , ("minus", minusV, Z :-> Z :-> Z)
    , ("plus", plusV, Z :-> Z :-> Z)
    , ("append", appendV, ZString :-> ZString :-> ZString)
    , ("lt", ltV, Z :-> Z :-> ZBool)
    , ("le", leV, Z :-> Z :-> ZBool)
    , ("gt", gtV, Z :-> Z :-> ZBool)
    , ("ge", geV, Z :-> Z :-> ZBool)
    , ("eq", eqV, Z :-> Z :-> ZBool)
    , ("ne", neV, Z :-> Z :-> ZBool)
    , ("and", andV, ZBool :-> ZBool :-> ZBool)
    , ("or", orV, ZBool :-> ZBool :-> ZBool)
    , ("e", eV, F)
    ]

parse :: String -> PuzzleM (P.A1 P.ParsingStage)
parse input = case P.parseAction' input of
  Left err -> throwError @String @PuzzleM $ "Parse error: " ++ show err
  Right ast -> pure ast

checkExtensions :: P.A1 P.ParsingStage -> PuzzleM (P.A1 P.ParsingStage)
checkExtensions = extensionCheckA1

typeCheck
  :: P.A1 P.ParsingStage
  -> PuzzleM [A PRunnerCtx]
typeCheck ast = do
  env <- getEnv
  (newEnv,as') <- case ast of
    P.Seq _ a as  -> tcAs env (a:as)
    P.OfA0 a -> tcAs env [a]
  modify (\s -> s { pstVarDict = newEnv })
  pure as'

eval :: [A PRunnerCtx] -> PuzzleM [A PRunnerCtx]
eval as = do
  evalE <- gets pstEvalE
  (newEnv, as') <- evalProgram evalE as
  modify (\s -> s { pstVarDict = newEnv })
  pure as'

interpret :: String -> PuzzleM String
interpret input = do
  mode <- case runParser parseChange P.initialPST "" input of
    Left _ -> pure Nothing
    Right m -> pure m
  case mode of
    Just UnsugaredInterpreter -> do
      m <- liftIO $ imap
      let basicExtensions = S.empty
      modify (\s -> s { pstVarDict = m, pstEnabledExtensions = basicExtensions, pstEvalE = evalEClassic })
      pure $ "ACK: Interpreter mode changed to zilly."
    Just ClassicInterpreter -> do
      m <- liftIO $ imapComplete
      let completeExtensions = S.fromList
            [ InfixFunctions
            , BoolType
            , RealType
            , TupleType
            , StringType
            , ArrayType
            , MultiParamApp
            , MultiParamLambda
            , ExtendedPrelude
            ]

      modify (\s -> s { pstVarDict = m, pstEnabledExtensions = completeExtensions, pstEvalE = evalE })
      pure $ "ACK: Interpreter mode changed to zilly+."
    Nothing -> do
       -- tas <- typeCheck =<< checkExtensions =<< parse input
       parsed <- parse input
       -- liftIO $ putStrLn $ "Parsed: " <> show parsed
       eChecked <- checkExtensions parsed
       -- liftIO $ putStrLn $ "Checked: " <> show eChecked
       tas <- typeCheck eChecked
       -- liftIO $ putStrLn $ "TypeChecked: " <> show tas
       as  <- eval tas
       let f x y = case (x,y) of
            (Print {},_) -> "OK: " <> show x <> " ==> " <> show y
            _            -> "ACK: " <> show x
       pure $ intercalate "\n" $ zipWith f tas as

buildInterpreter :: IO (String -> IO String)
buildInterpreter = do
  m <- imap
  let initialState = PuzzleState
        { pstIntSeed = 3
        , pstDoubleSeed = 0.1244541
        , pstCC = 0
        , pstVarDict = m
        , pstQ = 0
        , pstEnabledExtensions = S.empty
        , pstEvalE = evalEClassic
        }
  mst <- newMVar initialState
  pure $ \s -> catchError (do
    st <- takeMVar mst
    ma <- runPuzzleM st (interpret s)
    case ma of
      Left err -> putMVar mst st >> pure err
      Right (result,newST) -> do
          putMVar mst newST
          pure result) $ \e -> pure (show e)

ex1 :: IO ()
ex1 = genericEx "./programs/comparison.z"

ex2 :: IO ()
ex2 = genericEx "./programs/comparison_F.z"

ex3 :: IO ()
ex3 = genericEx "./programs/lazy1.z"

ex4 :: IO ()
ex4 = genericEx "./programs/lazy3.z"

ex5 :: IO ()
ex5 = genericEx "./programs/fibo.z"

ex6 :: IO ()
ex6 = genericEx "./programs/random.z"

ex7 :: IO ()
ex7 = genericEx "./programs/tuples.z"

ex8 :: IO ()
ex8 = genericEx "./programs/lazy_random.z"

ex9 :: IO ()
ex9 = genericEx "./programs/string.z"

ex10 :: IO ()
ex10 = genericEx "./programs/bool.z"

ex11 :: IO ()
ex11 = genericEx "./programs/floating.z"

ex12 :: IO ()
ex12 = genericEx "./programs/arithmetic.z"

ex13 :: IO ()
ex13 = genericEx "./programs/show.z"

ex14 :: IO ()
ex14 = genericEx "./programs/commands.z"

_1dSym :: IO ()
_1dSym = genericEx "./programs/ZillyArrays/1D.sym"

_2dSym :: IO ()
_2dSym = genericEx "./programs/ZillyArrays/2D.sym"

matMul :: IO ()
matMul = genericEx "./programs/ZillyArrays/matMul.sym"

stats :: IO ()
stats = genericEx "./programs/ZillyArrays/stats.sym"

slices :: IO ()
slices = genericEx "./programs/ZillyArrays/slices.sym"

unsugaredComplete :: IO ()
unsugaredComplete = genericEx "./programs/unsugared/complete.z"

genericEx :: FilePath -> IO ()
genericEx fp = do
  i  <- buildInterpreter
  fc <- lines <$> readFile fp
  traverse_ (putStrLn <=< i) . filter (any (\x -> x /= ' ' && x /= '\n' && x /= '\r') ) $ fc

rio :: IO ()
rio = randomIO @Int >>= print
