{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE RankNTypes            #-}

module Zilly.ZillyPlus.Tower where

import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Error 
import Zilly.ADT.Array 
import Zilly.ADT.Arithmetic 

import Zilly.ZillyPlus.Expression
import Zilly.ZillyPlus.Error 
import Zilly.ZillyPlus.Array 
import Zilly.ZillyPlus.Arithmetic 
import Zilly.ZillyPlus.Interpreter
import Utilities.LensM
import Utilities.TypedMapPlus
import Data.Proof
import Zilly.RValuePlus
import Zilly.Types
import Utilities.ShowM
import Zilly.UpcastPlus 
import Data.Singletons (SingI, sing, withSingI, Sing)
import Data.Coerce 
import Data.Sequence (Seq)


newtype ET a = ETower (E Void2 ErrorT  ExprTag a)

newtype ErrorT a = ErrorT (Error ET ArrayT ErrorTag a)

newtype ArrayT a = ArrayT (ArrayE ErrorT ArithmeticT ArrayTag a)

newtype ArithmeticT a = ArithmeticT (Arithmetic ArrayT Void2 ArithmeticTag a)

instance RValue Void2 a where
  type RVCtx Void2 = RVCtx (E Void2 ErrorT ExprTag)

instance  Biject Void2 a 
type instance Gamma (TaggedInterpreter ExprTag)       = TypeRepMap ErrorT ExprTag
type instance Gamma (TaggedInterpreter ErrorTag)      = Gamma (TaggedInterpreter ExprTag) 
type instance Gamma (TaggedInterpreter ArrayTag)      = Gamma (TaggedInterpreter ExprTag) 
type instance Gamma (TaggedInterpreter ArithmeticTag) = Gamma (TaggedInterpreter ExprTag) 

--------------------------------------------------------------------

instance  RValue ET (Value a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) = ETower <$> rvalue a

instance RValue ET (Array a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) =  ETower <$> rvalue a 

instance RValue ET (Lazy a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) =  ETower <$> rvalue a 

instance  RValue ET (LazyS a)  where 
  type RVCtx ET = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ETower a) = ETower <$> rvalue a 

---------------------------------------------------------------------


instance  RValue ErrorT (Value a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = ErrorT <$> rvalue a

instance  RValue ErrorT (Array a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) =  ErrorT <$> rvalue a 

instance  RValue ErrorT (Lazy a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = ErrorT <$> rvalue a 


instance  RValue ErrorT (LazyS a)  where 
  type RVCtx ErrorT = RVCtx (E Void2 ErrorT ExprTag)
  rvalue (ErrorT a) = ErrorT <$> rvalue a 

---------------------------------------------------------------------


instance  RValue ArrayT (Value a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = ArrayT <$> rvalue a

instance  RValue ArrayT (Array a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) =  ArrayT <$> rvalue a 

instance  RValue ArrayT (Lazy a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = ArrayT <$> rvalue a 

instance  RValue ArrayT (LazyS a)  where 
  type RVCtx ArrayT = RVCtx (E Void2 ArrayT ExprTag)
  rvalue (ArrayT a) = ArrayT <$> rvalue a 


--------------------------------------------------


type instance UpcastX ET a = UpcastX (E Void2 ErrorT ExprTag) a
type instance UpcastX ErrorT a = UpcastX (Error ET ArrayT ErrorTag) a
type instance UpcastX ArrayT a = UpcastX (ArrayE ErrorT ArithmeticT ArrayTag) a
type instance UpcastX ArithmeticT a = UpcastX (Arithmetic ArrayT Void2 ArithmeticTag) a


instance Upcast ET where 
  upcast :: forall (a :: Types) (b :: Types)  
    . (SingI a, SingI b)
    => UpcastX ET a  
    -> ET a  
    -> UpperBoundResults ET a b
  upcast d (ETower x) = case upcast @_ @a @b d x of 
    NonExistentUB -> NonExistentUB 
    SameTypeUB x' -> SameTypeUB $ ETower x' 
    LeftUB x'     -> LeftUB $ ETower x'
    RightUB x'    -> RightUB $ ETower x'
    SomethingElseUB x' -> SomethingElseUB $ ETower x'

instance Upcast ErrorT where 
  upcast :: forall (a :: Types) (b :: Types)  
    . (SingI a, SingI b)
    => UpcastX ErrorT a  
    -> ErrorT a  
    -> UpperBoundResults ErrorT a b
  upcast d (ErrorT x) = case upcast @_ @a @b d x of 
    NonExistentUB -> NonExistentUB 
    SameTypeUB x' -> SameTypeUB $ ErrorT x' 
    LeftUB x'     -> LeftUB $ ErrorT x'
    RightUB x'    -> RightUB $ ErrorT x'
    SomethingElseUB x' -> SomethingElseUB $ ErrorT x'

instance Upcast ArrayT where 
  upcast :: forall (a :: Types) (b :: Types)  
    . (SingI a, SingI b)
    => UpcastX ArrayT a  
    -> ArrayT a  
    -> UpperBoundResults ArrayT a b
  upcast d (ArrayT x) = case upcast @_ @a @b d x of 
    NonExistentUB -> NonExistentUB 
    SameTypeUB x' -> SameTypeUB $ ArrayT x' 
    LeftUB x'     -> LeftUB $ ArrayT x'
    RightUB x'    -> RightUB $ ArrayT x'
    SomethingElseUB x' -> SomethingElseUB $ ArrayT x'

instance Upcast ArithmeticT where 
  upcast :: forall (a :: Types) (b :: Types)  
    . (SingI a, SingI b)
    => UpcastX ArithmeticT a  
    -> ArithmeticT a  
    -> UpperBoundResults ArithmeticT a b
  upcast d (ArithmeticT x) = case upcast @_ @a @b d x of 
    NonExistentUB -> NonExistentUB 
    SameTypeUB x' -> SameTypeUB $ ArithmeticT x' 
    LeftUB x'     -> LeftUB $ ArithmeticT x'
    RightUB x'    -> RightUB $ ArithmeticT x'
    SomethingElseUB x' -> SomethingElseUB $ ArithmeticT x'


---------------------------------------------------------------------


instance  RValue ArithmeticT (Value a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a

instance  RValue ArithmeticT (Array a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a 

instance  RValue ArithmeticT (Lazy a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a 


instance  RValue ArithmeticT (LazyS a)  where 
  type RVCtx ArithmeticT = RVCtx (E Void2 ArithmeticT ExprTag)
  rvalue (ArithmeticT a) = ArithmeticT <$> rvalue a 



---------------------------------------------------------------------





voidShowProof :: forall m. Functor m => Dict (C (ShowM m) Void2)
voidShowProof = Dict

voidShowProof' :: forall m a. Functor m => Dict (ShowM m (Void2 a))
voidShowProof' = Dict


instance Monad m => ShowM m (ET a) where 
 showsPrecM p (ETower a) = showsPrecM p a

instance Monad m => ShowM m (ErrorT a) where 
   showsPrecM p (ErrorT a) = showsPrecM p a

instance Monad m => ShowM m (ArrayT a) where 
   showsPrecM p (ArrayT a) = showsPrecM p a

instance Monad m => ShowM m (ArithmeticT a) where 
  showsPrecM p (ArithmeticT a) = showsPrecM @m p a 



upcastET :: forall a. SingI a => UpcastX ET a 
upcastET = UpcastE 

upcastErrorT  :: forall a. 
  ( SingI a 
  ) => UpcastX ErrorT a
upcastErrorT =(upcastET,upcastArrayT, Dict,Dict,Dict)


upcastArrayT :: forall a. 
  ( SingI a
  ) => UpcastX ArrayT a 
upcastArrayT = UpcastArrayE sup sub 
  where 
  sup :: Zilly.ZillyPlus.Array.Exists ErrorT 
  sup = Zilly.ZillyPlus.Array.MkExists $ \(sx :: Sing x) ->  withSingI sx (upcastErrorT @x)

  sub :: Zilly.ZillyPlus.Array.Exists ArithmeticT 
  sub = Zilly.ZillyPlus.Array.MkExists $ \(sx :: Sing x) ->  withSingI sx (upcastArithmeticT @x)

upcastArithmeticT :: forall a. SingI a => UpcastX ArithmeticT a 
upcastArithmeticT = withSingIRType @a $ case sing @a of 
  SValue SZ -> 
    ( upcastArrayT
    , undefined
    , upcastArrayT
    , undefined
    , Dict
    , undefined
    , Dict
    , Dict
    , Dict
    , Dict
    , undefined
    )
  SValue SF ->
    ( upcastArrayT
    , undefined
    , upcastArrayT
    , undefined
    , Dict
    , undefined
    , Dict
    , Dict
    , Dict
    , Dict
    , undefined
    )
  SArray @sa sa -> withSingI sa $ case upcastArithmeticT @sa of
    (_,_,_,_,_,_,_,_,_,Dict,_) ->   
      ( upcastArrayT
      , undefined
      , upcastArrayT
      , undefined
      , Dict
      , undefined
      , Dict
      , Dict
      , Dict
      , Dict
      , undefined
      )
  _ -> error "impossible case"

instance Biject ET (Value F) where 
  project (ETower (Val (_,x,_))) = pure x 
  project _ = error "TODO"

  inject x = pure . ETower $ ValE x

instance Biject ErrorT (Value F) where 
  project (ErrorT (ErrorInh (a,_,_))) = project a 
  project (ErrorT (ErrorExp (a,_,_))) = project a 
  project _ = error "TODO"

  inject n = ErrorT . ErrorInhE <$> inject @ET n
  
instance Biject ArrayT (Value F) where 
  project (ArrayT (ArrayInh (a,_,_))) = project a 
  project (ArrayT (ArrayExp (a,_,_))) = project a 
  project _ = error "TODO"

  inject n = ArrayT . ArrayInhE <$> inject @ErrorT n


instance Biject ArithmeticT (Value F) where 
  project (ArithmeticT (ArithInh (a,_,_,_))) = project a 
  project (ArithmeticT (ArithExp (a,_,_,_))) = error "TODO"  
  project _ = error "TODO"


  inject n = ArithmeticT . ArithInhE <$> inject @ArrayT n


--------------------------



instance Biject ET (Value Z) where 
  project (ETower (Val (_,x,_))) = pure x 
  project _ = error "TODO"

  inject x = pure . ETower $ ValE x

instance Biject ErrorT (Value Z) where 
  project (ErrorT (ErrorInh (a,_,_))) = project a 
  project (ErrorT (ErrorExp (a,_,_))) = project a 
  project _ = error "TODO"

  inject n = ErrorT . ErrorInhE <$> inject @ET n
  
instance Biject ArrayT (Value Z) where 
  project (ArrayT (ArrayInh (a,_,_))) = project a 
  project (ArrayT (ArrayExp (a,_,_))) = project a 
  project _ = error "TODO"

  inject n = ArrayT . ArrayInhE <$> inject @ErrorT n


instance Biject ArithmeticT (Value Z) where 
  project (ArithmeticT (ArithInh (a,_,_,_))) = project a 
  project (ArithmeticT (ArithExp (a,_,_,_))) = error "TODO"  
  project _ = error "TODO"


  inject n = ArithmeticT . ArithInhE <$> inject @ArrayT n



------------------------------------


instance 
  ( Biject ArrayT a
  , SingI a 
  ) => Biject ET (Array a) where 
  project (ETower (Exp (x,_,_))) = project x 
  project _ = error "TODO"

  inject xs = ETower . ExpE <$> inject @ErrorT xs

instance 
  ( Biject ArrayT a
  , SingI a
  )=>  Biject ErrorT (Array a) where 
  project (ErrorT (ErrorInh (a,_,_))) = project a 
  project (ErrorT (ErrorExp (a,_,_))) = project a 
  project _ = error "TODO"

  inject n = ErrorT . ErrorExpE <$> inject @ArrayT n
  
instance 
  ( Biject ArrayT a
  , SingI a
  ) => Biject ArrayT (Array a) where 
  project (ArrayT (ArrayInh (a,_,_))) = project a 
  project (ArrayT (ArrayExp (a,_,_))) = project a 
  project (ArrayT (ArrayLiteral _ xs)) = traverse (project . ArrayT) xs
  project _ = error "TODO"

  inject xs =  ArrayT . ArrayLiteralE . fmap (\(ArrayT a) -> a) <$> traverse (inject @ArrayT) xs

withBijectArrayT :: forall a r. SingI a => (Biject ArrayT a => r) -> Maybe r
withBijectArrayT f = case sing @a of 
  SValue SZ -> pure f
  SValue SF -> pure f
  SArray @sa sa -> withSingI sa $ withBijectArrayT @sa f
  _ -> Nothing 


instance 
  ( Biject ArrayT a
  , SingI a
  ) => Biject ArithmeticT (Array a) where 
  project (ArithmeticT (ArithInh (a,_,_,_))) = project a 
  project (ArithmeticT (ArithExp (a,_,_,_))) = error "TODO"  
  project _ = error "TODO"


  inject n = ArithmeticT . ArithInhE <$> inject @ArrayT n


