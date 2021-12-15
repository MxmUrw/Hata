
module Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.Lattice where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Subsetoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Definition



---------------------------------------------------------------
-- We show that the preorder of ideals has finite meets
module _ {A : Monoid₀ 𝑖} where

  -- the top element
  instance
    isIdeal:⊤ : isIdeal A ⊤
    isIdeal.ideal-◍ isIdeal:⊤ = tt
    isIdeal.ideal-r-⋆ isIdeal:⊤ _ _ = tt

  ⊤-Ideal : Ideal A
  ⊤-Ideal = ′ ⊤ ′

  -- the meet
  instance
    isIdeal:∧ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Ideal A on I}} {{_ : Ideal A on J}} -> isIdeal A (′ I ′ ∧ ′ J ′)
    isIdeal:∧ = record
      { ideal-◍ = ideal-◍ , ideal-◍
      ; ideal-r-⋆ = λ (p , q) a -> ideal-r-⋆ p a , ideal-r-⋆ q a
      }

  _∧-Ideal_ : (I J : Ideal A) -> Ideal A
  _∧-Ideal_ I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′



  instance
    hasFiniteMeets:Ideal : hasFiniteMeets (Ideal A)
    hasFiniteMeets:Ideal = record
                              { ⊤          = ⊤-Ideal
                              ; terminal-⊤ = terminal-⊤
                              ; _∧_        = _∧-Ideal_
                              ; π₀-∧       = π₀-∧
                              ; π₁-∧       = π₁-∧
                              ; ⟨_,_⟩-∧    = ⟨_,_⟩-∧
                              }



---------------------------------------------------------------
-- We show that the preorder of ideals has finite joins
module _ {A : Monoid₀ 𝑖} where
  instance
    isIdeal:∨ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Ideal A on I}} {{_ : Ideal A on J}} -> isIdeal A (′ I ′ ∨ ′ J ′)
    isIdeal:∨ = record
                 { ideal-◍ = left ideal-◍
                 ; ideal-r-⋆ = λ x b → case x of
                                       (λ a∈I → left (ideal-r-⋆ a∈I b))
                                       (λ a∈J -> right (ideal-r-⋆ a∈J b))
                 }

  _∨-Ideal_ : (I J : Ideal A) -> Ideal A
  _∨-Ideal_ I J = ′ ⟨ I ⟩ ∨ ⟨ J ⟩ ′


module _ {Aᵘ : 𝒰 _} {{_ : Monoid₀ (𝑖 , 𝑖) on Aᵘ}} where

  private macro A = #structureOn Aᵘ

  -- the zero ideal
  record ⊥-Idealᵘ (a : A) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : a ∼ ◍

  open ⊥-Idealᵘ public

  macro ⊥-Ideal = #structureOn (↓𝒫 ⊥-Idealᵘ)

  -- it is a setoid
  instance
    isSetoid:⊥-Ideal : isSubsetoid ⊥-Ideal
    isSetoid:⊥-Ideal = record { transp-Subsetoid = t }
      where
        t : ∀{a b : A} -> a ∼ b -> ⊥-Idealᵘ a -> ⊥-Idealᵘ b
        t p (incl P) = incl (p ⁻¹ ∙ P)

  -- it is an ideal
  instance
    isIdeal:⊥-Ideal : isIdeal A ⊥-Ideal
    isIdeal:⊥-Ideal = record { ideal-◍ = P0 ; ideal-r-⋆ = P1 }
      where
        P0 : ⊥-Idealᵘ ◍
        P0 = incl refl

        P1 : ∀{a} -> ⊥-Idealᵘ a -> ∀ b -> ⊥-Idealᵘ (a ⋆ b)
        P1 {a} (incl p) b = incl q
          where
            q : (a ⋆ b) ∼ ◍
            q = a ⋆ b  ⟨ p ≀⋆≀ refl ⟩-∼
                ◍ ⋆ b  ⟨ absorb-l-⋆ ⟩-∼
                ◍      ∎

  -- it is the initial ideal
  initial-⊥-Ideal : ∀{I : Ideal A} -> ⊥-Ideal ≤ I
  initial-⊥-Ideal a = incl (λ (incl a∼◍) → transp-Subsetoid (a∼◍ ⁻¹) ideal-◍)

  ----------------------------------------------------------
  -- This means that the preorder of ideals has finite joins
  instance
    hasFiniteJoins:Ideal : hasFiniteJoins (Ideal A)
    hasFiniteJoins:Ideal = record
                              { ⊥          = ⊥-Ideal
                              ; initial-⊥  = λ {I} -> initial-⊥-Ideal {I = I}
                              ; _∨_        = _∨-Ideal_
                              ; ι₀-∨       = ι₀-∨
                              ; ι₁-∨       = ι₁-∨
                              ; [_,_]-∨    = [_,_]-∨
                              }


