
module Verification.Experimental.Data.Language.HindleyMilner.Type.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Module
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

ProductTheoryData = 𝕋×.統.𝒜


-------------------------------------------------
-- Definition of the data for the HM types

data 𝒹₀ : 𝒰₀ where
  tyᵗ : 𝒹₀

instance
  isDiscrete:𝒹₀ : isDiscrete 𝒹₀
  isDiscrete:𝒹₀ = record { _≟-Str_ = lem-1 }
    where
      lem-1 : (a b : 𝒹₀) → Decision (a ≡-Str b)
      lem-1 tyᵗ tyᵗ = yes refl-≣

data 𝒹₁ : List 𝒹₀ → 𝒹₀ → 𝒰 ℓ₀ where
  ⇒ᵗ : 𝒹₁ (tyᵗ ∷ tyᵗ ∷ []) tyᵗ
  ℕᵗ : 𝒹₁ [] tyᵗ
  𝔹ᵗ : 𝒹₁ [] tyᵗ

instance
  isDiscrete:𝒹₁ : ∀{xs : List 𝒹₀} {x : 𝒹₀} -> isDiscrete (𝒹₁ xs x)
  isDiscrete:𝒹₁ {xs} {x} = record { _≟-Str_ = lem-1 }
    where
      lem-1 : (a b : 𝒹₁ xs x) → Decision (a ≡-Str b)
      lem-1 ⇒ᵗ ⇒ᵗ = yes refl-≣
      lem-1 ℕᵗ ℕᵗ = yes refl-≣
      lem-1 ℕᵗ 𝔹ᵗ = no (λ ())
      lem-1 𝔹ᵗ ℕᵗ = no (λ ())
      lem-1 𝔹ᵗ 𝔹ᵗ = yes refl-≣

instance
  isSet:𝒹₀ : isSet-Str (𝒹₀)
  isSet:𝒹₀ = {!!}

𝒹 : ProductTheoryData _
𝒹 = record { Sort = 𝒹₀ ; Con = 𝒹₁ }






