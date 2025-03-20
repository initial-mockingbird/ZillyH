{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
-- {-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell          #-}

module Data.Nat where

import Data.Singletons.TH 
$(singletons [d|
  data Nat 
    = Zero 
    | Succ Nat 
  |])

