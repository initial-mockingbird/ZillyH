{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TC.HM where

import Zilly.Puzzle.Types.Exports qualified as T
import Zilly.Puzzle.Parser
import Zilly.Puzzle.TypeCheck.Unsugar
import Zilly.Puzzle.TypeCheck.HM
import Control.Monad.RWS
import Control.Monad.Except
import Control.Exception
import Control.Applicative (Alternative)
import Zilly.Puzzle.Action.Classes
import Data.Map (Map, (!), (!?))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text qualified as Text
import Data.String (IsString(..))
import Prelude.Singletons hiding (Map)
import GHC.TypeLits.Singletons
import Control.Monad.State.Strict
import Test.QuickCheck
import Debug.Trace (trace)

data HMTestState = HMTestState
  { typeVarCounter :: !Int
  , constraints :: [Constraint]
  , typeEnv :: Map String [(String,[T.Types])]
  , consEnv :: Map String (T.Types, [T.Types])
  }

data HMTestReader = HMTestReader
  { gammaEnv :: !Gamma

  }

data HMTestWriter = HMTestWriter
  { tcErrorLog :: [String]
  }

instance Semigroup HMTestWriter where
  (HMTestWriter e1) <> (HMTestWriter e2) = HMTestWriter (e1 <> e2)

instance Monoid HMTestWriter where
  mempty = HMTestWriter mempty

newtype HMTestM a = HMTestM
  { runHMTestM' :: ExceptT String (RWST HMTestReader HMTestWriter HMTestState IO) a
  } deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadIO
    , Alternative
    , MonadReader HMTestReader
    , MonadWriter HMTestWriter
    , MonadState HMTestState
    )

runHMTestM
  :: HMTestState
  -> HMTestReader
  -> HMTestM a
  -> IO (Either String a, HMTestState, HMTestWriter)
runHMTestM s r  (HMTestM m) = runRWST (runExceptT m) r s

instance MonadError String HMTestM where
  throwError = HMTestM . throwError
  catchError (HMTestM m) h = HMTestM (catchError m (runHMTestM' . h))

instance HasTypeEnv HMTestM where
  declareType _ _ = pure ()
  updateType _ _ = pure ()
  lookupType n = gets (M.lookup n . typeEnv)
  lookupCons n = gets (M.lookup n . consEnv)

instance InferMonad HMTestM where
  fresh = do
    s <- get
    let n = typeVarCounter s
    put s { typeVarCounter = n + 1 }
    return $ T.TVar (T.TV (Text.pack ("'a" ++ show n)))
  constraint c t = modify (\s -> s { constraints = EqConstraint c t : constraints s })
  gamma = asks gammaEnv
  getConstraints = gets constraints
  reportTCError err = tell (HMTestWriter [err])
  throwIrrecoverableError = throwError
  withVar n t = local (\r -> r { gammaEnv = M.insert (T.TV $ fromString n) t (gammaEnv r) })


data HMStage


data UntypedBoolExpr = BoolExpr
  { getUBE :: EPrec HMStage 0
  , ubeFreeVars :: Set String
  }

newtype UBEMonad a = UBEMonad
  { runUBEMonad :: State Int a
  } deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadState Int
    )


type instance EBX HMStage = ()
type instance EVX HMStage = ()
type instance EPX HMStage = ()
type instance EAndX HMStage = ()
type instance EOrX HMStage = ()
type instance ENegateX HMStage = ()
type instance EAppX HMStage = ()
type instance ELambdaX HMStage = ()

newtype VarGen = VarGen { getVarGen :: String }

instance Arbitrary VarGen where
  arbitrary = do
    n <- choose (1,3)
    chars <- vectorOf n (elements ['a'..'z'])
    pure $ VarGen chars

instance Arbitrary UntypedBoolExpr where
  arbitrary = do
    let f = PParen () . getUBE
    let fbLit = do
            trace "fbLit" (pure ())
            b <- arbitrary @Bool
            pure $ BoolExpr { getUBE = OfHigher0 $ PBool @HMStage () b, ubeFreeVars = mempty}
    let fbVar = do
            trace "fbVar" (pure ())
            x <- getVarGen <$> arbitrary

            pure $ BoolExpr { getUBE = OfHigher0 $ PVar @HMStage () x, ubeFreeVars = S.singleton x}
    let fNot = do
            trace "fNot" (pure ())
            e <- arbitrary @UntypedBoolExpr
            let e' = PNegate @HMStage () $ OfHigherPrefixPrec @Atom @HMStage (f e)
            pure $ BoolExpr { getUBE = OfHigher0 e', ubeFreeVars = ubeFreeVars e}
    let fAnd  = do
          trace "fAnd" (pure ())
          e1 <- arbitrary @UntypedBoolExpr
          e2 <- arbitrary @UntypedBoolExpr
          let e1' = f e1
          let e2' = f e2
          pure $ BoolExpr
            { getUBE = OfHigher0 $ PAnd @Atom @HMStage () e1' (OfHigher3 e2')
            , ubeFreeVars = S.union (ubeFreeVars e1) (ubeFreeVars e2)
            }
    let fOr   = do
          trace "fOr" (pure ())
          e1 <- arbitrary @UntypedBoolExpr
          e2 <- arbitrary @UntypedBoolExpr
          let e1' = f e1
          let e2' = f e2
          pure $ BoolExpr
            { getUBE = OfHigher0 $ POr @Atom @HMStage () e1' (OfHigher3 e2')
            , ubeFreeVars = S.union (ubeFreeVars e1) (ubeFreeVars e2)
            }
    let abs = do
          trace "abs" (pure ())
          bodyUBE <- arbitrary @UntypedBoolExpr
          x <- case S.toList $ ubeFreeVars bodyUBE of
            fvars@(_:_) -> elements fvars
            [] -> getVarGen <$> arbitrary
          let var = OfHigher0 $ PVar @HMStage () x
          let body = f  bodyUBE
          pure $ BoolExpr
            { getUBE = OfHigher0 $ PLambda @HMStage () [(var, T.ZBool)] Nothing (OfHigher1 body)
            , ubeFreeVars = S.delete x (ubeFreeVars bodyUBE)
            }
    let app1 = do
          trace "app1" (pure ())
          fun <- abs
          arg <- arbitrary @UntypedBoolExpr
          let arg' = getUBE arg
          let fun' = OfHigherPostfixPrec $ PParen () (getUBE fun)
          let app  = PApp @HMStage () fun' [arg']
          pure $ BoolExpr
            { getUBE = OfHigher0 app
            , ubeFreeVars = S.union (ubeFreeVars fun) (ubeFreeVars arg)
            }

    let fs =
          [ fbLit
          , fbVar
          , fNot
          , fAnd
          , fOr
          -- , app1

          ]


    frequency $ zip [1,1,1,1,1,1] fs

tcBoolFirstOrder :: HMTestState -> (Set String -> HMTestReader) -> Property
tcBoolFirstOrder initialState initialReader = forAllShow (arbitrary @UntypedBoolExpr) show' prop
  where
    show' :: UntypedBoolExpr -> String
    show' (BoolExpr e _) = show e

    prop (BoolExpr e fvs) = ioProperty $ do
      let run = do
            -- liftIO $ putStrLn $ "expression: " <> show e
            te  <- infer e
            -- liftIO $ putStrLn $ "type before solving: " <> show te
            cs <- gets constraints
            -- liftIO $ putStrLn $ "constraints: " <> show cs
            substs <- solve emptySubst cs
            -- liftIO $ putStrLn $ "substitutions: " <> show substs
            let tes = apply substs te
            -- liftIO $ putStrLn $ "type after solving: " <> show tes
            pure (te,tes,cs,substs)
      (res, finalState, log) <- runHMTestM initialState (initialReader fvs) run
      case res of
        Left err -> pure . flip counterexample False
          $ "Type error: "
          <> err
          <> "\nLog:\n"
          <> unlines (tcErrorLog log)
        Right (te,tes,cs,substs)  -> do
          liftIO . putStrLn
            $ "Expression: \n"
            <> show e
            <> "\nInferred type: "
            <> show tes
            <> "\nType before substitutions: "
            <> show te
            <>  "\nConstraints: "
            <> show cs
            <> "\nSubstitutions: "
            <> show substs
            <> "\nLog:\n"
            <> unlines (tcErrorLog log)
          pure $ property True



props :: [Property]
props =
  [ label "Type check boolean expressions (first-order)"
    $ tcBoolFirstOrder initialState initialReader
  , label "Type check boolean expressions (first-order, no bindings)"
    $ tcBoolFirstOrder initialState noBindingsReader
  ]
  where
  initialState = HMTestState
    { typeVarCounter = 0
    , constraints = []
    , typeEnv = M.fromList
        [
        ]
    , consEnv = M.fromList
        [
        ]
    }
  initialReader = \fvs -> HMTestReader
    { gammaEnv =  M.fromList [(T.TV (fromString v), Forall S.empty T.ZBool) | v <- S.toList fvs]
    }
  noBindingsReader = \_ -> HMTestReader { gammaEnv = mempty }
