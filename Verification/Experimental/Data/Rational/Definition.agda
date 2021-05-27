
module Verification.Experimental.Data.Rational.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Ring.Localization

private
  ℤ⁺ : 𝒫 ℤ
  ℤ⁺ a = ∑ λ b -> a ≡-Str (pos (suc b))

instance
  isSubsetoid:ℤ⁺ : isSubsetoid ℤ⁺
  isSubsetoid.transp-Subsetoid isSubsetoid:ℤ⁺ (incl p) (b , refl-StrId) = {!!} , {!!}

instance
  isMCS:ℤ⁺ : isMCS ′ ℤ ′ ′ ℤ⁺ ′
  isMCS.closed-⋅ isMCS:ℤ⁺ = {!!}
  isMCS.closed-⨡ isMCS:ℤ⁺ = {!!}

instance
  hasNotZero-MCS:ℤ⁺ : hasNotZero-MCS ′ ℤ⁺ ′
  hasNotZero-MCS:ℤ⁺ = {!!}

ℚ = Localize ′ ℤ ′ ′ ℤ⁺ ′

-- ta tb : ℚ
-- ta = pos 1 / (pos 2 ∈ (1 , it))

-- tb = negsuc 23 / (pos 3 ∈ (2 , it))

-- tc = ta ⋆ tb


