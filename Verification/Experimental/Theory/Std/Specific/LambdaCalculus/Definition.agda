
module Verification.Experimental.Theory.Std.Specific.LambdaCalculus.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF


data Sort-𝕋Λ : 𝒰₀ where
  tyᵗ ctxᵗ : Sort-𝕋Λ

data Con-Type-𝕋× : List Sort-𝕋Λ → Sort-𝕋Λ → 𝒰 ℓ₀ where
  ⇒ᵗ : Con-Type-𝕋× (tyᵗ ∷ tyᵗ ∷ []) tyᵗ
  ℕᵗ : Con-Type-𝕋× [] tyᵗ
  𝔹ᵗ : Con-Type-𝕋× [] tyᵗ
  []ᵗ : Con-Type-𝕋× [] ctxᵗ
  ,,ᵗ : Con-Type-𝕋× (ctxᵗ ∷ tyᵗ ∷ []) ctxᵗ


TypeAxiom-𝕋Λ : ProductTheory ℓ₀
Sort TypeAxiom-𝕋Λ = Sort-𝕋Λ
isDiscrete:Sort TypeAxiom-𝕋Λ = {!!}
isSet-Str:Sort TypeAxiom-𝕋Λ = {!!}
Con TypeAxiom-𝕋Λ = Con-Type-𝕋×
isDiscrete:Con TypeAxiom-𝕋Λ = {!!}

Type-𝕋Λ : 𝒰₀
Type-𝕋Λ = Term₁-𝕋× TypeAxiom-𝕋Λ ◌ tyᵗ

module _ where -- §-Type-𝕋Λ-Example where
  e1 : Type-𝕋Λ
  e1 = con ℕᵗ ◌-⧜

  e2 : Type-𝕋Λ
  e2 = con 𝔹ᵗ ◌-⧜

x = unify (⧜subst (incl e1)) (⧜subst (incl e2))









