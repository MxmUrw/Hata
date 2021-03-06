
module Verification.Conventions.Meta2.EqChainMacros where

-- open import Verification.Conventions hiding (β²_β²) public
open import Verification.Conventions.Meta2.Structure public

open import Verification.Conventions.Meta.Term
open import Verification.Conventions.Meta.Universe
open import Verification.Conventions.Prelude hiding (β²_β²)

record Rec (A : π° π) : π° π where
  constructor rec
  field el : A

open Rec {{...}} public

instance
  Rec:β : Rec β
  Rec:β = rec 2

  Rec:πΉ : Rec Bool
  Rec:πΉ = rec true


macro
  getrec : Term -> Term -> TC π-π°
  getrec t hole = do
    Ο <- inferType hole

    let res = def (quote el) ([])

    unify hole res

    return tt

myval : β
myval = getrec true

inferUniverse : Type -> TC π
inferUniverse Ο = do
  agda-sort (set a) <- inferType Ο
    where _ -> typeError (strErr "expected universe" β· [])
  π <- unquoteTC a
  return π

macro
  both-βΌ : Term -> Term -> TC π-π°
  both-βΌ path hole = do
    let a1 = def (quote _β»ΒΉ) (varg path β· [])
    let a2 = var 0 []
    let a3 = path
    let a12  = def (quote _β_) (varg a1 β· varg a2 β· [])
    let a123 = def (quote _β_) (varg a12 β· varg a3 β· [])
    let res = lam visible (Abs.abs "ΞΎ" a123)
    Ο <- (inferType hole)

    -- π <- inferUniverse Ο
    -- Ο' <- unquoteTC Ο >> TC (π° π) <<
    -- uterm <- unquoteTC res >> TC Ο' <<
    -- term' <- quoteTC uterm
    -- r <- (checkType term' Ο)
    -- res' <- withNormalisation true (checkType res Ο)
    unify hole res
    return tt
    -- r <- withReconstructed (checkType res Ο)
    -- unify hole r

