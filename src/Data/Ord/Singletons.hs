{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE PackageImports           #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeAbstractions #-}
module Data.Ord.Singletons 
  (module All) where

import "singletons-base" Data.Ord.Singletons qualified as All hiding (Ord(..))
import Prelude.Singletons
import Data.Kind (Constraint)
import Data.Proof
import Data.Singletons.TH
import GHC.Base (undefined)


$(singletons [d|
  data Ordering' a b 
    = EQ'
    | LT'
    | GT'
  |])

compare' :: forall {k} (a :: k) (b :: k) c. 
  (SDecide k, SingI a, SingI b,SOrd k) 
  => (a ~ b => c) 
  -> ((a < b) ~ True => c)
  -> ((b < a) ~ True => c)
  -> c
compare' eqF ltF gtF = case sing @a %~ sing @b of
  Proved Refl  -> eqF 
  Disproved _  -> case (sing @a  %< sing @b) %~ STrue of
     Proved Refl  -> ltF
     Disproved _  -> case (sing @b  %< sing @a) %~ STrue of
      Proved Refl  -> gtF
      Disproved _  -> undefined  
