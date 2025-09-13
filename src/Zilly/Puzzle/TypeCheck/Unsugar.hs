{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE GADTs               #-}

module Zilly.Puzzle.TypeCheck.Unsugar
  ( unsugarE
  ) where

import Zilly.Puzzle.Parser


import Prelude.Singletons
import Data.Singletons.TH
import Data.Matchers

unsugarE :: forall n ctx. SingI n => EPrec ctx n -> EPrec ctx n
unsugarE e = case () of
  ()  | Just Refl <- matches @0 (sing @n) -> unsugarE0 e
      | Just Refl <- matches @1 (sing @n) -> unsugarE1 e
      | Just Refl <- matches @3 (sing @n) -> unsugarE3 e
      | Just Refl <- matches @4 (sing @n) -> unsugarE4 e
      | Just Refl <- matches @6 (sing @n) -> unsugarE6 e
      | Just Refl <- matches @7 (sing @n) -> unsugarE7 e
      | Just Refl <- matches @8 (sing @n) -> unsugarE8 e
      | Just Refl <- matches @PrefixPrec (sing @n) -> unsugarEPrefixPrec e
      | Just Refl <- matches @PostfixPrec (sing @n) -> unsugarEPostfixPrec e
      | Just Refl <- matches @Atom (sing @n) -> unsugarEAtom e
      | otherwise -> error $ "unsugarE: unsupported type " ++ show (sing @n)




unsugarEAtom :: EPrec ctx Atom -> EPrec ctx Atom
unsugarEAtom (PInt bk a)    = PInt bk a
unsugarEAtom (PFloat bk a)  = PFloat bk a
unsugarEAtom (PBool bk a)   = PBool bk a
unsugarEAtom (PString bk a) = PString bk a
unsugarEAtom (PVar bk a)    = PVar bk a
unsugarEAtom (PTuple bk a b xs)
  = PTuple bk (unsugarE a) (unsugarE b) (unsugarE <$> xs)
unsugarEAtom (PParen bk a) = PParen bk (unsugarE a)
unsugarEAtom (PIf bk (a,b,c))
  = PIf bk (unsugarE a, unsugarE b, unsugarE c)
unsugarEAtom (PDefer bk a)
  = PDefer bk (unsugarE a)
unsugarEAtom (PArray bk xs)
  = PArray bk (unsugarE <$> xs)
unsugarEAtom (PMatch bk e branches)
  = PMatch bk (unsugarE e) [(unsugarPattern p, unsugarE b) | (p,b) <- branches]
  where
    unsugarPatternGuard :: PPaternGuard ctx -> PPaternGuard ctx
    unsugarPatternGuard (PExprGuard bk e) = PExprGuard bk (unsugarE e)
    unsugarPatternGuard (PBindingGuard bk lp e)
      = PBindingGuard bk lp (unsugarE e)

    unsugarPattern :: PPattern ctx -> PPattern ctx
    unsugarPattern (MkPPattern lp guards) =
      MkPPattern lp (unsugarPatternGuard <$> guards)
unsugarEAtom (PECons bk s es)
  = PECons bk s (unsugarE <$> es)
unsugarEAtom (PEARecord bk fields) =
  PEARecord bk [(k, unsugarE v) | (k,v) <- fields]
unsugarEPrefixPrec :: EPrec ctx PrefixPrec -> EPrec ctx PrefixPrec
unsugarEPrefixPrec (PUMinus bk a) = PUMinus bk (unsugarE a)
unsugarEPrefixPrec (PNegate bk a) = PNegate bk (unsugarE a)
unsugarEPrefixPrec (OfHigherPrefixPrec a)
  = OfHigherPrefixPrec (unsugarE a)

unsugarEPostfixPrec :: EPrec ctx PostfixPrec -> EPrec ctx PostfixPrec
unsugarEPostfixPrec (PApp bk f (x1:x2:xs))
  = unsugarEPostfixPrec $ PApp bk (PApp bk f [x1]) (x2:xs)
unsugarEPostfixPrec (PApp bk f xs)
  = PApp bk (unsugarE f) (unsugarE <$> xs)
unsugarEPostfixPrec (PAppArr bk f (x1:x2:xs))
  = unsugarEPostfixPrec $ PAppArr bk (PAppArr bk f [x1]) (x2:xs)
unsugarEPostfixPrec (PAppArr bk f xs)
  = PAppArr bk (unsugarE f) (unsugarIndexer <$> xs)
unsugarEPostfixPrec (PDotApp bk e field)
  = PDotApp bk (unsugarE e) field
unsugarEPostfixPrec (OfHigherPostfixPrec a)
  = OfHigherPostfixPrec (unsugarE a)

unsugarIndexer :: PIndexerExpression ctx -> PIndexerExpression ctx
unsugarIndexer (PIndex a)
  = PIndex (unsugarE a)
unsugarIndexer (PRangeIndexer (a,b))
  = PRangeIndexer (unsugarE a, unsugarE b)

unsugarE8 :: EPrec ctx 8 -> EPrec ctx 8
unsugarE8 (PPower bk a b)
  = PPower bk (unsugarE a) (unsugarE b)
unsugarE8 (OfHigher8 a)
  = OfHigher8 (unsugarE a)

unsugarE7 :: EPrec ctx 7 -> EPrec ctx 7
unsugarE7 (PMul bk a b)
  = PMul bk (unsugarE a) (unsugarE b)
unsugarE7 (PDiv bk a b)
  = PDiv bk (unsugarE a) (unsugarE b)
unsugarE7 (PMod bk a b)
  = PMod bk (unsugarE a) (unsugarE b)
unsugarE7 (OfHigher7 a)
  = OfHigher7 (unsugarE a)

unsugarE6 :: EPrec ctx 6 -> EPrec ctx 6
unsugarE6 (PPlus bk a b)
  = PPlus bk (unsugarE a) (unsugarE b)
unsugarE6 (PMinus bk a b)
  = PMinus bk (unsugarE a) (unsugarE b)
unsugarE6 (PAppend bk a b)
  = PAppend bk (unsugarE a) (unsugarE b)
unsugarE6 (OfHigher6 a)
  = OfHigher6 (unsugarE a)

unsugarE4 :: EPrec ctx 4 -> EPrec ctx 4
unsugarE4 (PLT bk a b)
  = PLT bk (unsugarE a) (unsugarE b)
unsugarE4 (PLTEQ bk a b)
  = PLTEQ bk (unsugarE a) (unsugarE b)
unsugarE4 (PGT bk a b)
  = PGT bk (unsugarE a) (unsugarE b)
unsugarE4 (PGTEQ bk a b)
  = PGTEQ bk (unsugarE a) (unsugarE b)
unsugarE4 (PEQ bk a b)
  = PEQ bk (unsugarE a) (unsugarE b)
unsugarE4 (PNEQ bk a b)
  = PNEQ bk (unsugarE a) (unsugarE b)
unsugarE4 (OfHigher4 a)
  = OfHigher4 (unsugarE a)

unsugarE3 :: EPrec ctx 3 -> EPrec ctx 3
unsugarE3 (PAnd bk a b)
  = PAnd bk (unsugarE a) (unsugarE b)
unsugarE3 (POr bk a b)
  = POr bk (unsugarE a) (unsugarE b)
unsugarE3 (OfHigher3 a)
  = OfHigher3 (unsugarE a)


unsugarE1 :: EPrec ctx 1 -> EPrec ctx 1
unsugarE1 (PLambda bk (a1:a2:as) _ body)
  = unsugarE1
  $ PLambda bk [a1] Nothing
  $ PLambda bk (a2:as) Nothing (body)
unsugarE1 (PLambda bk args mret body)
  = PLambda bk ((\(e,t) -> (unsugarE e,t)) <$> args) mret (unsugarE body)
unsugarE1 (OfHigher1 a)
  = OfHigher1 (unsugarE a)

unsugarE0 :: EPrec ctx 0 -> EPrec ctx 0
unsugarE0 (OfHigher0 a)
  = OfHigher0 (unsugarE a)
