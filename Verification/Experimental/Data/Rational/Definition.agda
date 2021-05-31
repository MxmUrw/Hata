
module Verification.Experimental.Data.Rational.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Ring.Localization
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.Preorder

private
  ℤ⁺ : 𝒫 ℤ
  ℤ⁺ a = ∣ (∑ λ b -> a ≡-Str (pos (suc b))) ∣

instance
  isSubsetoid:ℤ⁺ : isSubsetoid ℤ⁺
  isSubsetoid.transp-Subsetoid isSubsetoid:ℤ⁺ (incl p) (b , refl-StrId) = {!!} , {!!}

instance
  isMCS:ℤ⁺ : isMCS ℤ ′ ℤ⁺ ′
  isMCS.closed-⋅ isMCS:ℤ⁺ = {!!}
  isMCS.closed-⨡ isMCS:ℤ⁺ = {!!}

instance
  hasNotZero-MCS:ℤ⁺ : hasNotZero-MCS ′ ℤ⁺ ′
  hasNotZero-MCS:ℤ⁺ = {!!}

Rational = Localize ℤ ′ ℤ⁺ ′

macro
  ℚ : SomeStructure
  ℚ = #structureOn Rational

instance
  hasReprHasPositiveDenom:ℚ : hasRepr ℚ hasPositiveDenom
  hasReprHasPositiveDenom:ℚ = record
    { repr = lem-10
    }
    where
      lem-10 : ∀ (a : ℚ) -> Repr hasPositiveDenom a
      lem-10 (a / (pos n ∢ (x , refl-StrId))) = record
        { ⟨_⟩ = (a / pos n ∢ (x , refl-StrId))
        ; represents = refl
        ; hasProperty = incl (λ {(incl (pos Sx≤0)) → ¬-<-zero ⟨ Sx≤0 ⟩})
        }

instance
  isUnbound:ℚ : isUnbound ℚ
  isUnbound:ℚ = record
    { getLess = λ q -> (q ⋆ ◡ (embed-Localize 1)) ∢ {!!}
    ; getGreater = λ q -> (q ⋆ (embed-Localize 1)) ∢ {!!}
    }

inv-ℚ : (a : ℚ) -> (a ≁ ◌) -> ℚ
inv-ℚ (a0 / (a1 ∢ _)) p = a1 / (a0 ∢ {!!})

instance
  isDense:ℚ : isDense ℚ
  isDense:ℚ = record
    { between = λ {a} {b} (a<b) -> (b ⋆ (◡ a)) ⋅ (inv-ℚ (embed-Localize 2) {!!}) ∢ {!!}
    }


-- ta tb : ℚ
-- ta = pos 1 / (pos 2 ∈ (1 , it))

-- tb = negsuc 23 / (pos 3 ∈ (2 , it))

-- tc = ta ⋆ tb


