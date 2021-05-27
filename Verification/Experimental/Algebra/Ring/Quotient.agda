
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Ring.Quotient where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition



-- module _ {R : 𝒰 _} {I : 𝒫 R} {{_ : Ring 𝑗 on R}} {{_ : Ideal ′ R ′ on I}} where
module _ {𝑗 : 𝔏 ^ 2} {R : Ring 𝑗} {I : Ideal R} where
  -- blabla : isCommutative ′ ⟨ R ⟩ ′
  -- blabla = it
  -- X = ⟨ (′ ⟨ R ⟩ ′) /-Abelian ′ ⟨ I ⟩ ′ ⟩

  instance
    isSemiring:Quot : isSemiring ′ (⟨ R ⟩) /-𝒰 RelIdeal I ′
    -- isSemiring:Quot : isSemiring ′ ⟨ (′ R ′) /-Abelian ′ I ′ ⟩ ′
    isSemiring._⋅_ isSemiring:Quot [ a ] [ b ] = [ a ⋅ b ]
    isSemiring.⨡ isSemiring:Quot = [ ⨡ ]
    isSemiring.unit-l-⋅ isSemiring:Quot {a = [ a ]} = preserves-∼ unit-l-⋅
    isSemiring.unit-r-⋅ isSemiring:Quot {a = [ a ]} = preserves-∼ unit-r-⋅
    isSemiring.assoc-l-⋅ isSemiring:Quot {a = [ a ]} {b = [ b ]} {c = [ c ]} = preserves-∼ assoc-l-⋅
    isSemiring.distr-l-⋅ isSemiring:Quot {a = [ a ]} {b = [ b ]} {c = [ c ]} = preserves-∼ distr-l-⋅
    isSemiring.distr-r-⋅ isSemiring:Quot {a = [ a ]} {b = [ b ]} {c = [ c ]} = preserves-∼ distr-r-⋅
    isSemiring._`cong-⋅`_ isSemiring:Quot {a₀ = [ a₀ ]} {a₁ = [ a₁ ]} {b₀ = [ b₀ ]} {b₁ = [ b₁ ]} (incl (incl p)) (incl (incl q)) =
      let P₀ : ⟨ ⟨ I ⟩ ((a₀ ⋆ ◡ a₁) ⋅ b₀) ⟩
          P₀ = ideal-r-⋅ p

          P₁ : ∀{x y z} -> ((x ⋆ ◡ y) ⋅ z) ∼ x ⋅ z ⋆ ◡ (y ⋅ z)
          P₁ {x} {y} {z} =
               ((x ⋆ ◡ y) ⋅ z) ≣⟨ distr-r-⋅ ⟩
               (x ⋅ z ⋆ ◡ y ⋅ z) ≣⟨ refl `cong-⋆` switch-◡-⋅-l ⁻¹ ⟩
               x ⋅ z ⋆ ◡ (y ⋅ z) ∎

          P₂ : ⟨ ⟨ I ⟩ (a₀ ⋅ b₀ ⋆ ◡ (a₁ ⋅ b₀)) ⟩
          P₂ = transp-Subsetoid P₁ P₀

          P₃ : ∀{x y z} -> (z ⋅ (x ⋆ ◡ y)) ∼ z ⋅ x ⋆ ◡ (z ⋅ y)
          P₃ {x} {y} {z} =
               (z ⋅ (x ⋆ ◡ y)) ≣⟨ distr-l-⋅ ⟩
               (z ⋅ x ⋆ z ⋅ ◡ y) ≣⟨ refl `cong-⋆` switch-◡-⋅-r ⁻¹ ⟩
               z ⋅ x ⋆ ◡ (z ⋅ y) ∎

          P₄ : ⟨ ⟨ I ⟩ (a₁ ⋅ b₀ ⋆ ◡ (a₁ ⋅ b₁)) ⟩
          P₄ = transp-Subsetoid P₃ (ideal-l-⋅ q)

          P₅ : ⟨ ⟨ I ⟩ ((a₀ ⋅ b₀ ⋆ ◡ (a₁ ⋅ b₀)) ⋆ (a₁ ⋅ b₀ ⋆ ◡ (a₁ ⋅ b₁))) ⟩
          P₅ = closed-⋆ P₂ P₄

          P₆ : ∀ {x y z} -> (x ⋆ ◡ y) ⋆ (y ⋆ z) ∼ x ⋆ z
          P₆ {x} {y} {z} =
            (x ⋆ ◡ y) ⋆ (y ⋆ z)   ≣⟨ assoc-l-⋆ ⟩
            x ⋆ (◡ y ⋆ (y ⋆ z))   ≣⟨ refl `cong-⋆` assoc-r-⋆ ⟩
            x ⋆ (◡ y ⋆ y ⋆ z)     ≣⟨ refl `cong-⋆` ((inv-l-⋆ `cong-⋆` refl) ∙ unit-l-⋆) ⟩
            x ⋆ z                 ∎

          P₇ : ⟨ ⟨ I ⟩ (a₀ ⋅ b₀ ⋆ ◡ (a₁ ⋅ b₁)) ⟩
          P₇ = transp-Subsetoid P₆ P₅
      in incl (incl P₇)

    -- isRing:Quot : isRing ′ ⟨ (′ R ′) /-Abelian ′ I ′ ⟩ ′
    -- -- isRing:Quot : isRing ′ ⟨ (′ ⟨ R ⟩ ′) /-Abelian ′ ⟨ I ⟩ ′ ⟩ ′
    -- isRing:Quot = record {}

-- _/-Ring_ : (R : Ring 𝑗) -> (I : Ideal R) -> Ring _
-- _/-Ring_ R I = ′ ⟨ ′ ⟨ R ⟩ ′ /-Abelian ′ ⟨ I ⟩ ′ ⟩ ′


