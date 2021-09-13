
module Verification.Experimental.Order.WellFounded.Construction.Product where

open import Verification.Conventions
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Order.WellFounded.Definition

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} (R : A -> A -> 𝒰 𝑘) (S : B -> B -> 𝒰 𝑙) where
  ×-≪ : (A × B) -> (A × B) -> 𝒰 (𝑘 ､ 𝑙)
  ×-≪ (a , b) (a2 , b2) = R a a2 × S b b2

  private T = ×-≪

  module _ (p : WellFounded R) (q : WellFounded S) where
    private
      lem-3 : ∀ a b -> Acc R a -> Acc S b -> Acc T (a , b)
      lem-3 a b (acc racc) (acc sacc) = acc λ (a1 , b1) (r1 , s1) → lem-3 a1 b1 (racc a1 r1) (sacc b1 s1)

      lem-1 : ∀ x -> Acc T x
      lem-1 (a0 , b0) = lem-3 a0 b0 (p a0) (q b0)

    WellFounded:× : WellFounded T
    WellFounded:× = lem-1

module _ {A : 𝒰 𝑖} {{_ : isWF 𝑗 A}}
         {B : 𝒰 𝑘} {{_ : isWF 𝑙 B}} where
  instance
    isWF:× : isWF _ (A × B)
    isWF:× = record { _≪_ = ×-≪ _≪_ _≪_ ; wellFounded = WellFounded:× _≪_ _≪_ wellFounded wellFounded }

  module _ {{_ : isWFT ′ A ′}} {{_ : isWFT ′ B ′}} where
    instance
      isWFT:× : isWFT (A × B)
      isWFT:× = record { _⟡-≪_ = λ (p0 , p1) (q0 , q1) → (p0 ⟡-≪ q0) , (p1 ⟡-≪ q1) }

instance
  isWF:𝟙 : isWF _ (𝟙-𝒰)
  isWF:𝟙 = record { _≪_ = (λ a b -> ⊥-𝒰 {ℓ₀}) ; wellFounded = λ x → acc λ _ () }

  isWFT:𝟙 : isWFT ′ 𝟙-𝒰 ′
  isWFT:𝟙 = record { _⟡-≪_ = λ () }

  isWFT0:𝟙 : isWFT0 ′ 𝟙-𝒰 ′
  isWFT0:𝟙 = record { ⊥-WFT = tt ; initial-⊥-WFT = left refl-≣ }

    -- module _ {{_ : isWFT0 ′ A ′}} {{_ : isWFT0 ′ B ′}} where
    --   private
    --     ⊥' : A × B
    --     ⊥' = ⊥-WFT , ⊥-WFT

    --     lem-1 : ∀{a : A} {b : B} -> ⊥' ⪣ (a , b)
    --     lem-1 {a} {b} with initial-⊥-WFT {a = a} | initial-⊥-WFT {a = b}
    --     ... | left refl-≣ | left refl-≣ = left refl-≣
    --     ... | left x | just x₁ = {!!}
    --     ... | just x | Y = {!!}

    --   instance
    --     isWFT0:Lexi : isWFT0 (A × B)
    --     isWFT0:Lexi = record { ⊥-WFT = ⊥' ; initial-⊥-WFT = lem-1 }



