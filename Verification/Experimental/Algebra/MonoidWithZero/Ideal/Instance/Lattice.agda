
module Verification.Experimental.Algebra.MonoidWithZero.Ideal.Instance.Lattice where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Ideal.Definition



---------------------------------------------------------------
-- We show that the preorder of ideals has finite meets
module _ {A : Monoid₀ 𝑖} where

  -- the top element
  instance
    isIdealᵣ:⊤ : isIdealᵣ A ⊤
    isIdealᵣ.ideal-◍ isIdealᵣ:⊤ = tt
    isIdealᵣ.ideal-r-⋆ isIdealᵣ:⊤ _ _ = tt

  ⊤-Idealᵣ : Idealᵣ A
  ⊤-Idealᵣ = ′ ⊤ ′

  -- the meet
  instance
    isIdealᵣ:∧ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Idealᵣ A on I}} {{_ : Idealᵣ A on J}} -> isIdealᵣ A (′ I ′ ∧ ′ J ′)
    isIdealᵣ:∧ = record
      { ideal-◍ = ideal-◍ , ideal-◍
      ; ideal-r-⋆ = λ (p , q) a -> ideal-r-⋆ p a , ideal-r-⋆ q a
      }

  _∧-Idealᵣ_ : (I J : Idealᵣ A) -> Idealᵣ A
  _∧-Idealᵣ_ I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′



  instance
    hasFiniteMeets:Idealᵣ : hasFiniteMeets (Idealᵣ A)
    hasFiniteMeets:Idealᵣ = record
                              { ⊤          = ⊤-Idealᵣ
                              ; terminal-⊤ = terminal-⊤
                              ; _∧_        = _∧-Idealᵣ_
                              ; π₀-∧       = π₀-∧
                              ; π₁-∧       = π₁-∧
                              ; ⟨_,_⟩-∧    = ⟨_,_⟩-∧
                              }



---------------------------------------------------------------
-- We show that the preorder of ideals has finite joins
module _ {A : Monoid₀ 𝑖} where
  instance
    isIdealᵣ:∨ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Idealᵣ A on I}} {{_ : Idealᵣ A on J}} -> isIdealᵣ A (′ I ′ ∨ ′ J ′)
    isIdealᵣ:∨ = record
                 { ideal-◍ = left ideal-◍
                 ; ideal-r-⋆ = λ x b → case x of
                                       (λ a∈I → left (ideal-r-⋆ a∈I b))
                                       (λ a∈J -> right (ideal-r-⋆ a∈J b))
                 }

  _∨-Idealᵣ_ : (I J : Idealᵣ A) -> Idealᵣ A
  _∨-Idealᵣ_ I J = ′ ⟨ I ⟩ ∨ ⟨ J ⟩ ′


module _ {Aᵘ : 𝒰 _} {{_ : Monoid₀ (𝑖 , 𝑖) on Aᵘ}} where

  private macro A = #structureOn Aᵘ

  -- the zero ideal
  record ⊥-Idealᵣᵘ (a : A) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : a ∼ ◍

  open ⊥-Idealᵣᵘ public

  macro ⊥-Idealᵣ = #structureOn (↓𝒫 ⊥-Idealᵣᵘ)

  -- it is a setoid
  instance
    isSetoid:⊥-Idealᵣ : isSubsetoid ⊥-Idealᵣ
    isSetoid:⊥-Idealᵣ = record { transp-Subsetoid = t }
      where
        t : ∀{a b : A} -> a ∼ b -> ⊥-Idealᵣᵘ a -> ⊥-Idealᵣᵘ b
        t p (incl P) = incl (p ⁻¹ ∙ P)

  -- it is an ideal
  instance
    isIdealᵣ:⊥-Idealᵣ : isIdealᵣ A ⊥-Idealᵣ
    isIdealᵣ:⊥-Idealᵣ = record { ideal-◍ = P0 ; ideal-r-⋆ = P1 }
      where
        P0 : ⊥-Idealᵣᵘ ◍
        P0 = incl refl

        P1 : ∀{a} -> ⊥-Idealᵣᵘ a -> ∀ b -> ⊥-Idealᵣᵘ (a ⋆ b)
        P1 {a} (incl p) b = incl q
          where
            q : (a ⋆ b) ∼ ◍
            q = a ⋆ b  ⟨ p ≀⋆≀ refl ⟩-∼
                ◍ ⋆ b  ⟨ absorb-l-⋆ ⟩-∼
                ◍      ∎

  -- it is the initial ideal
  initial-⊥-Idealᵣ : ∀{I : Idealᵣ A} -> ⊥-Idealᵣ ≤ I
  initial-⊥-Idealᵣ a = incl (λ (incl a∼◍) → transp-Subsetoid (a∼◍ ⁻¹) ideal-◍)

  ----------------------------------------------------------
  -- This means that the preorder of ideals has finite joins
  instance
    hasFiniteJoins:Idealᵣ : hasFiniteJoins (Idealᵣ A)
    hasFiniteJoins:Idealᵣ = record
                              { ⊥          = ⊥-Idealᵣ
                              ; initial-⊥  = λ {I} -> initial-⊥-Idealᵣ {I = I}
                              ; _∨_        = _∨-Idealᵣ_
                              ; ι₀-∨       = ι₀-∨
                              ; ι₁-∨       = ι₁-∨
                              ; [_,_]-∨    = [_,_]-∨
                              }


