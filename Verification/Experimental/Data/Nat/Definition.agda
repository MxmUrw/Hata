
module Verification.Experimental.Data.Nat.Definition where

open import Verification.Experimental.Conventions renaming (ℕ to Nat)

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Totalorder

macro
  ℕ : SomeStructure
  ℕ = #structureOn Nat

-- instance
--   isSetoid:ℕ : isSetoid _ ℕ
--   isSetoid._∼'_ isSetoid:ℕ = _≣_
--   isSetoid.isEquivRel:∼ isSetoid:ℕ = it

instance
  isMonoid:ℕ : isMonoid ℕ
  isMonoid:ℕ = record
                 { _⋆_ = _+-ℕ_
                 ; ◌ = 0
                 ; unit-l-⋆ = refl
                 ; unit-r-⋆ = {!!}
                 ; assoc-l-⋆ = {!!}
                 -- ; assoc-r-⋆ = {!!}
                 ; _`cong-⋆`_ = {!!}
                 }

instance
  isCommutative:ℕ : isCommutative ℕ
  isCommutative:ℕ = {!!}


instance
  isPreorder:ℕ : isPreorder _ ′ ℕ ′
  isPreorder._≤_ isPreorder:ℕ = ≤-Base _≤-ℕ_
  isPreorder.reflexive isPreorder:ℕ = incl refl-≤-ℕ
  isPreorder._⟡_ isPreorder:ℕ (incl p) (incl q) = incl (trans-≤-ℕ p q)
  isPreorder.transp-≤ isPreorder:ℕ (refl-StrId) (refl-StrId) r = r
  -- incl (transport (λ i -> p i ≤-ℕ q i) r)

instance
  isPartialorder:ℕ : isPartialorder ℕ
  isPartialorder:ℕ = record
    { antisym = λ p q -> (antisym-≤-ℕ ⟨ p ⟩ ⟨ q ⟩)
    }

instance
  isTotalorder⁺:ℕ : isTotalorder⁺ ℕ
  isTotalorder⁺:ℕ = record
    { total⁺ = lem-10
    }
    where
      lem-5 : ∀ {a b} -> (a <-ℕ b) -> a ∼ b -> 𝟘-𝒰
      lem-5 p (refl-StrId) = ¬m<m p

      lem-10 : ∀ a b -> Trichotomy' ℕ a b
      lem-10 a b with a ≟-ℕ b
      ... | lt x = lt (incl (<-weaken x) , lem-5 x)
      ... | eq x = eq (x)
      ... | gt x = gt (incl (<-weaken x) , lem-5 x)


instance
  isDiscrete:ℕ : isDiscrete ℕ
  isDiscrete:ℕ = record { _≟-Str_ = discreteℕ }

instance
  isSet-Str:ℕ : isSet-Str ℕ
  isSet-Str:ℕ = {!!}



monotone-l-⋆-ℕ : ∀{a b c : ℕ} -> a ≤ b -> c ⋆ a ≤ c ⋆ b
monotone-l-⋆-ℕ {a} {b} {c} (incl (b-a , bap)) = incl (b-a , p)
  where
    p : b-a +-ℕ (c +-ℕ a) ≣ c +-ℕ b
    p = b-a +-ℕ (c +-ℕ a)   ⟨ refl {x = b-a} ≀⋆≀ comm-⋆ {a = c} {a} ⟩-∼
        b-a +-ℕ (a +-ℕ c)   ⟨ assoc-r-⋆ {a = b-a} {b = a} {c = c} ⟩-∼
        (b-a +-ℕ a) +-ℕ c   ⟨ bap ≀⋆≀ refl {x = c} ⟩-∼
        b ⋆ c                ⟨ comm-⋆ {a = b} ⟩-∼
        c ⋆ b                ∎



