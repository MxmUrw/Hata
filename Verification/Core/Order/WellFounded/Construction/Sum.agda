
module Verification.Core.Order.WellFounded.Construction.Sum where

open import Verification.Conventions
open import Verification.Core.Set.Induction.WellFounded
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Order.WellFounded.Definition


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isWF 𝑘 A}} {{_ : isWF 𝑙 B}} where
  data +-≪ : (A + B) -> (A + B) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑙) where
    left : ∀{a0 a1 : A} -> a0 ≪ a1 -> +-≪ (left a0) (left a1)
    right : ∀{b0 b1 : B} -> b0 ≪ b1 -> +-≪ (right b0) (right b1)
    left-right : ∀{a : A} {b : B} -> +-≪ (left a) (right b)

  private
    lem-1 : ∀{a : A} -> Acc _≪_ a -> Acc +-≪ (left a)
    lem-1 {a} (acc p) = acc (λ {y (left x) → lem-1 (p _ x)})

    lem-1b : ∀{b : B} -> Acc _≪_ b -> Acc +-≪ (right b)
    lem-1b {b} (acc p) = acc (λ { y (right x) → lem-1b (p _ x)
                                ; y (left-right) -> lem-1 (wellFounded _)})


    lem-2 : WellFounded +-≪
    lem-2 (left x) = lem-1 (wellFounded _)
    lem-2 (just x) = lem-1b (wellFounded _)

  instance
    isWF:+ : isWF _ (A + B)
    isWF:+ = record { _≪_ = +-≪ ; wellFounded = lem-2 }


  module _ {{_ : isWFT ′ A ′}} {{_ : isWFT ′ B ′}} where
    lem-3 : {a b c : A +-𝒰 B} → +-≪ a b → +-≪ b c → +-≪ a c
    lem-3 (left x) (left y) = left (x ⟡-≪ y)
    lem-3 (left x) left-right = left-right
    lem-3 (right x) (right y) = right (x ⟡-≪ y)
    lem-3 left-right (right x) = left-right

    instance
      isWFT:+ : isWFT (A + B)
      isWFT:+ = record { _⟡-≪_ = lem-3 }


    module _ {{_ : isWFT0 ′ A ′}} where
      private
        ⊥' : A + B
        ⊥' = left ⊥-WFT
        lem-4 : ∀{a : A + B} -> ⊥' ⪣ a
        lem-4 {left x} with initial-⊥-WFT {a = x}
        ... | left refl-≣ = left refl-≣
        ... | just p = right (left p)
        lem-4 {just x} = right left-right

      instance
        isWFT0:+ : isWFT0 (A + B)
        isWFT0:+ = record
          { ⊥-WFT = ⊥'
          ; initial-⊥-WFT = lem-4
          }

