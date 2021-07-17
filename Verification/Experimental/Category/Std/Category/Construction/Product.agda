
module Verification.Experimental.Category.Std.Category.Construction.Product where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Data.Fin.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Construction.Id
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Morphism.Iso


--------------------------------------------------------------
-- Showing that _×_ on universes lifts to categories

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


  -- currently special treatment for isomorphisms
  into-×-≅ : ∀{a b : 𝒞} {c d : 𝒟} -> (p : a ≅ b) (q : c ≅ d) -> (a , c) ≅ (b , d)
  into-×-≅ p q = (⟨ p ⟩ , ⟨ q ⟩) since P
    where
      P = record
          { inverse-◆  = (inverse-◆ (of p) , inverse-◆ (of q))
          ; inv-r-◆    = inv-r-◆ (of p) , inv-r-◆ (of q)
          ; inv-l-◆    = inv-l-◆ (of p) , inv-l-◆ (of q)
          }

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  π₀-𝐂𝐚𝐭 : Functor (𝒞 × 𝒟) 𝒞
  π₀-𝐂𝐚𝐭 = fst since P
    where
      P : isFunctor _ _ fst
      isFunctor.map P              = fst
      isFunctor.isSetoidHom:map P  = record { cong-∼ = fst }
      isFunctor.functoriality-id P = refl
      isFunctor.functoriality-◆ P  = refl

  π₁-𝐂𝐚𝐭 : Functor (𝒞 × 𝒟) 𝒟
  π₁-𝐂𝐚𝐭 = snd since P
    where
      P : isFunctor _ _ snd
      isFunctor.map P              = snd
      isFunctor.isSetoidHom:map P  = record { cong-∼ = snd }
      isFunctor.functoriality-id P = refl
      isFunctor.functoriality-◆ P  = refl

module _ {𝒳 : Category 𝑖} {𝒞 : Category 𝑗} {𝒟 : Category 𝑘} where
  ⟨_,_⟩-𝐂𝐚𝐭 : (F : Functor 𝒳 𝒞) -> (G : Functor 𝒳 𝒟) -> Functor 𝒳 (𝒞 × 𝒟)
  ⟨_,_⟩-𝐂𝐚𝐭 F G = h since P
    where
      h : ⟨ 𝒳 ⟩ -> 𝒞 × 𝒟
      h x = ⟨ F ⟩ x , ⟨ G ⟩ x

      P : isFunctor _ _ h
      isFunctor.map P              = λ ϕ -> map ϕ , map ϕ
      isFunctor.isSetoidHom:map P  = record { cong-∼ = λ p -> cong-∼ p , cong-∼ p }
      isFunctor.functoriality-id P = functoriality-id , functoriality-id
      isFunctor.functoriality-◆ P  = functoriality-◆ , functoriality-◆

  module _ {F : Functor 𝒳 𝒞} {G : Functor 𝒳 𝒟} where
    reduce-π₀-𝐂𝐚𝐭 : (⟨ F , G ⟩-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭) ≅ F
    reduce-π₀-𝐂𝐚𝐭 = α since P
      where
        α : Natural (⟨ F , G ⟩-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭) F
        α = id since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = F}}})

        β : Natural F (⟨ F , G ⟩-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭)
        β = id since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = F}}})

        P : isIso (hom α)
        P = record
            { inverse-◆  = β
            ; inv-r-◆    = unit-2-◆
            ; inv-l-◆    = unit-2-◆
            }

    reduce-π₁-𝐂𝐚𝐭 : (⟨ F , G ⟩-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭) ≅ G
    reduce-π₁-𝐂𝐚𝐭 = α since P
      where
        α : Natural (⟨ F , G ⟩-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭) G
        α = id since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = G}}})

        β : Natural G (⟨ F , G ⟩-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭)
        β = id since natural (naturality {{of id-𝐅𝐮𝐧𝐜 {F = G}}})

        P : isIso (hom α)
        P = record
            { inverse-◆  = β
            ; inv-r-◆    = unit-2-◆
            ; inv-l-◆    = unit-2-◆
            }

  module _ {F : Functor 𝒳 (𝒞 × 𝒟)} where
    expand-×-𝐂𝐚𝐭 : F ≅ ⟨ F ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭 , F ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭 ⟩-𝐂𝐚𝐭
    expand-×-𝐂𝐚𝐭 = α since P
      where
        α : Natural F ⟨ F ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭 , F ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭 ⟩-𝐂𝐚𝐭
        α = (id , id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹ , unit-l-◆ ∙ unit-r-◆ ⁻¹)

        β : Natural ⟨ F ◆-𝐂𝐚𝐭 π₀-𝐂𝐚𝐭 , F ◆-𝐂𝐚𝐭 π₁-𝐂𝐚𝐭 ⟩-𝐂𝐚𝐭 F
        β = (id , id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹ , unit-l-◆ ∙ unit-r-◆ ⁻¹)

        P : isIso (hom α)
        P = record
            { inverse-◆  = β
            ; inv-r-◆    = unit-2-◆ , unit-2-◆
            ; inv-l-◆    = unit-2-◆ , unit-2-◆
            }

--------------------------------------------------------------
-- The 0-ary product, 𝟙

instance
  isCategory:𝟙 : isCategory (⊤-𝒰 {𝑖})
  isCategory:𝟙 = isCategory:byId



