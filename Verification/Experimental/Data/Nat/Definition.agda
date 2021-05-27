
module Verification.Experimental.Data.Nat.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Preorder


instance
  isSetoid:ℕ : isSetoid _ ℕ
  isSetoid._∼'_ isSetoid:ℕ = _≡_
  isSetoid.isEquivRel:∼ isSetoid:ℕ = it


instance
  isPreorder:ℕ : isPreorder _ ′ ℕ ′
  isPreorder._≤'_ isPreorder:ℕ = _≤-ℕ_
  isPreorder.reflexive isPreorder:ℕ = incl refl-≤-ℕ
  isPreorder._⟡_ isPreorder:ℕ (incl p) (incl q) = incl (trans-≤-ℕ p q)
  isPreorder.transp-≤ isPreorder:ℕ (incl p) (incl q) (incl r) = incl (transport (λ i -> p i ≤-ℕ q i) r)

Preorder:ℕ : Preorder _
Preorder:ℕ = ′ ℕ ′


instance
  isDiscrete:ℕ : isDiscrete ℕ
  isDiscrete:ℕ = {!!}

instance
  isSet-Str:ℕ : isSet-Str ℕ
  isSet-Str:ℕ = {!!}


