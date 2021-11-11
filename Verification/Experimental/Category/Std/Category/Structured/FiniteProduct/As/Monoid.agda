
module Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition


module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is FiniteProductCategory 𝑖}} where

  private instance
    _ : isSetoid 𝒞
    _ = isSetoid:byCategory

    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:⧼⧽

  private
    lem-1 : ∀{a b : 𝒞} -> a ⊓ b ∼ b ⊓ a
    lem-1 {a} {b} = f since P
      where
        f : a ⊓ b ⟶ b ⊓ a
        f = ⧼ π₁ , π₀ ⧽

        g : b ⊓ a ⟶ a ⊓ b
        g = ⧼ π₁ , π₀ ⧽

        P₀ : f ◆ g ∼ id
        P₀ = f ◆ g                             ⟨ expand-⊓ ⟩-∼
             ⧼ (f ◆ g) ◆ π₀ , (f ◆ g) ◆ π₁ ⧽   ⟨ cong-∼ (assoc-l-◆ , assoc-l-◆) ⟩-∼
             ⧼ f ◆ (g ◆ π₀) , f ◆ (g ◆ π₁) ⧽   ⟨ cong-∼ (refl ◈ reduce-π₀ , refl ◈ reduce-π₁) ⟩-∼
             ⧼ f ◆ π₁ , f ◆ π₀ ⧽               ⟨ cong-∼ (reduce-π₁ ∙ unit-l-◆ ⁻¹ , reduce-π₀ ∙ unit-l-◆ ⁻¹) ⟩-∼
             ⧼ id ◆ π₀ , id ◆ π₁ ⧽             ⟨ expand-⊓ ⁻¹ ⟩-∼
             id                                ∎

        P₁ : g ◆ f ∼ id
        P₁ = g ◆ f                             ⟨ expand-⊓ ⟩-∼
             ⧼ (g ◆ f) ◆ π₀ , (g ◆ f) ◆ π₁ ⧽   ⟨ cong-∼ (assoc-l-◆ , assoc-l-◆) ⟩-∼
             ⧼ g ◆ (f ◆ π₀) , g ◆ (f ◆ π₁) ⧽   ⟨ cong-∼ (refl ◈ reduce-π₀ , refl ◈ reduce-π₁) ⟩-∼
             ⧼ g ◆ π₁ , g ◆ π₀ ⧽               ⟨ cong-∼ (reduce-π₁ ∙ unit-l-◆ ⁻¹ , reduce-π₀ ∙ unit-l-◆ ⁻¹) ⟩-∼
             ⧼ id ◆ π₀ , id ◆ π₁ ⧽             ⟨ expand-⊓ ⁻¹ ⟩-∼
             id                                ∎

        P : isIso (hom f)
        P = record
            { inverse-◆ = g
            ; inv-r-◆   = P₀
            ; inv-l-◆   = P₁
            }

    lem-2 : ∀{a : 𝒞} -> ⊤ ⊓ a ∼ a
    lem-2 {a} = π₁ since P
      where
        g : a ⟶ ⊤ ⊓ a
        g = ⧼ intro-⊤ , id ⧽

        P₀ : π₁ ◆ g ∼ id
        P₀ = π₁ ◆ g                             ⟨ expand-⊓ ⟩-∼
             ⧼ (π₁ ◆ g) ◆ π₀ , (π₁ ◆ g) ◆ π₁ ⧽  ⟨ cong-∼ (assoc-l-◆ , assoc-l-◆) ⟩-∼
             ⧼ π₁ ◆ (g ◆ π₀) , π₁ ◆ (g ◆ π₁) ⧽  ⟨ cong-∼ (refl ◈ reduce-π₀ , refl ◈ reduce-π₁ ) ⟩-∼
             ⧼ π₁ ◆ intro-⊤ , π₁ ◆ id ⧽         ⟨ cong-∼ (expand-⊤ ∙ expand-⊤ ⁻¹ ∙ unit-l-◆ ⁻¹ , unit-r-◆ ∙ unit-l-◆ ⁻¹) ⟩-∼
             ⧼ id ◆ π₀ , id ◆ π₁ ⧽              ⟨ expand-⊓ ⁻¹ ⟩-∼
             id                                 ∎

        P : isIso (hom π₁)
        P = record
            { inverse-◆ = g
            ; inv-r-◆   = P₀
            ; inv-l-◆   = reduce-π₁
            }

    lem-3 : ∀{a b c : 𝒞} -> (a ⊓ b) ⊓ c ∼ a ⊓ (b ⊓ c)
    lem-3 {a} {b} {c} = f since P
      where
        f : (a ⊓ b) ⊓ c ⟶ a ⊓ (b ⊓ c)
        f = ⧼ π₀ ◆ π₀ , ⧼ π₀ ◆ π₁ , π₁ ⧽ ⧽

        g : a ⊓ (b ⊓ c) ⟶ (a ⊓ b) ⊓ c
        g = ⧼ ⧼ π₀ , π₁ ◆ π₀ ⧽ , π₁ ◆ π₁ ⧽


        P = record
            { inverse-◆ = g
            ; inv-r-◆   = {!!}
            ; inv-l-◆   = {!!}
            }




  isMonoid:byHasFiniteProducts : isMonoid ′ 𝒞 ′
  isMonoid:byHasFiniteProducts = record
    { _⋆_        = _⊓_
    ; ◌          = ⊤
    ; unit-l-⋆   = lem-2
    ; unit-r-⋆   = lem-1 ∙ lem-2
    ; assoc-l-⋆  = lem-3
    ; _`cong-⋆`_ = {!!}
    }



