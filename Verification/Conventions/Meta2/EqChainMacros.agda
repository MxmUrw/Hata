
module Verification.Conventions.Meta2.EqChainMacros where

-- open import Verification.Conventions hiding (′_′) public
open import Verification.Conventions.Meta2.Structure public

open import Verification.Conventions.Meta.Term
open import Verification.Conventions.Meta.Universe
open import Verification.Conventions.Prelude hiding (′_′)

record Rec (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor rec
  field el : A

open Rec {{...}} public

instance
  Rec:ℕ : Rec ℕ
  Rec:ℕ = rec 2

  Rec:𝔹 : Rec Bool
  Rec:𝔹 = rec true


macro
  getrec : Term -> Term -> TC 𝟙-𝒰
  getrec t hole = do
    τ <- inferType hole

    let res = def (quote el) ([])

    unify hole res

    return tt

myval : ℕ
myval = getrec true

inferUniverse : Type -> TC 𝔏
inferUniverse τ = do
  agda-sort (set a) <- inferType τ
    where _ -> typeError (strErr "expected universe" ∷ [])
  𝑖 <- unquoteTC a
  return 𝑖

macro
  both-∼ : Term -> Term -> TC 𝟙-𝒰
  both-∼ path hole = do
    let a1 = def (quote _⁻¹) (varg path ∷ [])
    let a2 = var 0 []
    let a3 = path
    let a12  = def (quote _∙_) (varg a1 ∷ varg a2 ∷ [])
    let a123 = def (quote _∙_) (varg a12 ∷ varg a3 ∷ [])
    let res = lam visible (Abs.abs "ξ" a123)
    τ <- (inferType hole)

    -- 𝑖 <- inferUniverse τ
    -- τ' <- unquoteTC τ >> TC (𝒰 𝑖) <<
    -- uterm <- unquoteTC res >> TC τ' <<
    -- term' <- quoteTC uterm
    -- r <- (checkType term' τ)
    -- res' <- withNormalisation true (checkType res τ)
    unify hole res
    return tt
    -- r <- withReconstructed (checkType res τ)
    -- unify hole r

