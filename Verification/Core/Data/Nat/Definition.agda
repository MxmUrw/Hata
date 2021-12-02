
module Verification.Core.Data.Nat.Definition where

open import Verification.Core.Conventions renaming (ℕ to Nat)

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder

ℕᵘ = Nat

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
                 ; _≀⋆≀_ = {!!}
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
    p = b-a +-ℕ (c +-ℕ a)   ⟨ refl {a = b-a} ≀⋆≀ comm-⋆ {a = c} {a} ⟩-∼
        b-a +-ℕ (a +-ℕ c)   ⟨ assoc-r-⋆ {a = b-a} {b = a} {c = c} ⟩-∼
        (b-a +-ℕ a) +-ℕ c   ⟨ bap ≀⋆≀ refl {a = c} ⟩-∼
        b ⋆ c                ⟨ comm-⋆ {a = b} ⟩-∼
        c ⋆ b                ∎







