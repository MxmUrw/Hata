
module Verification.Core.Data.List.Variant.Binary.Naturaliant.Binary.Natural where

open import Verification.Core.Conventions renaming (ℕ to Nat)

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Data.List.Variant.Binary
open import Verification.Core.Order.Preorder


人ℕᵘ : 𝒰₀
人ℕᵘ = ⋆List ⊤-𝒰

macro 人ℕ = #structureOn 人ℕᵘ

ι-人ℕ : Nat -> 人ℕ
ι-人ℕ zero = ◌
ι-人ℕ (suc n) = incl tt ⋆ ι-人ℕ n

instance
  fromNat人ℕ : HasFromNat 人ℕ
  fromNat人ℕ = record { Constraint = λ _ → 𝟙-𝒰 ; fromNat = λ n -> ι-人ℕ n }


record _≤-人ℕ_ (a b : 人ℕ) : 𝒰₀ where
  constructor _,_
  field fst : 人ℕ
  field snd : a ⋆ fst ∼ b

open _≤-人ℕ_ public

reflexive-人ℕ : ∀{a} -> a ≤-人ℕ a
reflexive-人ℕ = ◌ , unit-r-⋆

_⟡-人ℕ_ : ∀{a b c} -> a ≤-人ℕ b -> b ≤-人ℕ c -> a ≤-人ℕ c
_⟡-人ℕ_ {a} {b} {c} (b-a , p) (c-b , q) = (b-a ⋆ c-b) , r
  where
    r : a ⋆ (b-a ⋆ c-b) ∼ c
    r = a ⋆ (b-a ⋆ c-b)  ⟨ assoc-r-⋆ ⟩-∼
        (a ⋆ b-a) ⋆ c-b  ⟨ p ≀⋆≀ refl ⟩-∼
        b ⋆ c-b          ⟨ q ⟩-∼
        c                ∎


instance
  isPreorder:♮ℕ : isPreorder _ 人ℕ
  isPreorder:♮ℕ = record { _≤_ = _≤-人ℕ_ ; reflexive = reflexive-人ℕ ; _⟡_ = _⟡-人ℕ_ ; transp-≤ = {!!} }


private
  lem-1 : ∀{a : 人ℕ} {t : ⊤-𝒰} -> incl t ⋆ a ∼ a ⋆ incl t
  lem-1 {incl tt} {tt} = refl
  lem-1 {a ⋆-⧜ b} {t} = p
    where
      p : incl t ⋆ (a ⋆ b) ∼ (a ⋆ b) ⋆ incl t
      p = incl t ⋆ (a ⋆ b) ⟨ assoc-r-⋆ ⟩-∼
          (incl t ⋆ a) ⋆ b ⟨ lem-1 ≀⋆≀ refl ⟩-∼
          a ⋆ incl t ⋆ b   ⟨ assoc-l-⋆ ⟩-∼
          a ⋆ (incl t ⋆ b) ⟨ refl ≀⋆≀ lem-1 ⟩-∼
          a ⋆ (b ⋆ incl t) ⟨ assoc-r-⋆ ⟩-∼
          a ⋆ b ⋆ incl t   ∎

  lem-1 {◌-⧜} {t} = unit-r-⋆ ∙ unit-l-⋆ ⁻¹

comm-⋆-人ℕ : ∀{a b : 人ℕ} -> (a ⋆ b) ∼ b ⋆ a
comm-⋆-人ℕ {incl x} {b} = lem-1
comm-⋆-人ℕ {a ⋆-⧜ b} {c} = p ⁻¹
  where
    p : c ⋆ (a ⋆ b) ∼ (a ⋆ b) ⋆ c
    p = c ⋆ (a ⋆ b) ⟨ assoc-r-⋆ ⟩-∼
        (c ⋆ a) ⋆ b ⟨ comm-⋆-人ℕ ≀⋆≀ refl ⟩-∼
        a ⋆ c ⋆ b   ⟨ assoc-l-⋆ ⟩-∼
        a ⋆ (c ⋆ b) ⟨ refl ≀⋆≀ comm-⋆-人ℕ ⟩-∼
        a ⋆ (b ⋆ c) ⟨ assoc-r-⋆ ⟩-∼
        a ⋆ b ⋆ c   ∎
comm-⋆-人ℕ {◌-⧜} {b} = unit-l-⋆ ∙ unit-r-⋆ ⁻¹

instance
  isCommutative:人ℕ : isCommutative 人ℕ
  isCommutative:人ℕ = record { comm-⋆ = comm-⋆-人ℕ }


-- instance
--   isPreorder:人ℕ : isPreorder _ 人ℕ
--   isPreorder._≤'_ isPreorder:人ℕ = {!!}
--   isPreorder.reflexive isPreorder:人ℕ = {!!}
--   isPreorder._⟡_ isPreorder:人ℕ = {!!}
--   isPreorder.transp-≤ isPreorder:人ℕ = {!!}


monotone-l-⋆-人ℕ : ∀{a b c : 人ℕ} -> a ≤ b -> c ⋆ a ≤ c ⋆ b
monotone-l-⋆-人ℕ {a} {b} {c} (b-a , bap) = (b-a , p)
  where
    p : (c ⋆ a) ⋆ b-a ∼ c ⋆ b
    p = (c ⋆ a) ⋆ b-a ⟨ assoc-l-⋆ ⟩-∼
        c ⋆ (a ⋆ b-a) ⟨ refl ≀⋆≀ bap ⟩-∼
        c ⋆ b         ∎



