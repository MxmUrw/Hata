
module Verification.Experimental.Category.Std.Category.Construction.Product where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Data.Fin.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑗₁} B}} where
  instance
    isSetoid:× : isSetoid (A × B)
    isSetoid:× = setoid (λ (a₀ , b₀) (a₁ , b₁) -> (a₀ ∼ a₁) × (b₀ ∼ b₁))
                 (refl , refl)
                 (λ (p , q) -> (p ⁻¹ , q ⁻¹))
                 (λ (p₀ , q₀) (p₁ , q₁) -> (p₀ ∙ p₁ , q₀ ∙ q₁))

module _ {𝒞 : 𝒰 𝑖} {𝒟 : 𝒰 𝑗} {{_ : isCategory {𝑖₁} 𝒞}} {{_ : isCategory {𝑗₁} 𝒟}} where

  instance
    isCategory:× : isCategory (𝒞 × 𝒟)
    isCategory.Hom isCategory:× = λ (a , b) (c , d) -> (a ⟶ c) × (b ⟶ d)
    isCategory.isSetoid:Hom isCategory:× = isSetoid:×
    isCategory.id isCategory:×         = id , id
    isCategory._◆_ isCategory:×        = λ (f₀ , g₀) (f₁ , g₁) -> (f₀ ◆ f₁ , g₀ ◆ g₁)
    isCategory.unit-l-◆ isCategory:×   = unit-l-◆ , unit-l-◆
    isCategory.unit-r-◆ isCategory:×   = unit-r-◆ , unit-r-◆
    isCategory.unit-2-◆ isCategory:×   = unit-2-◆ , unit-2-◆
    isCategory.assoc-l-◆ isCategory:×  = assoc-l-◆ , assoc-l-◆
    isCategory.assoc-r-◆ isCategory:×  = assoc-r-◆ , assoc-r-◆
    isCategory._◈_ isCategory:×        = λ (p₀ , q₀) (p₁ , q₁) -> (p₀ ◈ p₁ , q₀ ◈ q₁)

  into-×-≅ : ∀{a b : 𝒞} {c d : 𝒟} -> (p : a ≅ b) (q : c ≅ d) -> (a , c) ≅ (b , d)
  into-×-≅ p q = (⟨ p ⟩ , ⟨ q ⟩) since P
    where
      P = record
          { inverse-◆  = (inverse-◆ (of p) , inverse-◆ (of q))
          ; inv-r-◆    = inv-r-◆ (of p) , inv-r-◆ (of q)
          ; inv-l-◆    = inv-l-◆ (of p) , inv-l-◆ (of q)
          }


