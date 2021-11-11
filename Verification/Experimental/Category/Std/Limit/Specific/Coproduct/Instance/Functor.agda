
module Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Functor where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Morphism.Epi.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.Definition

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{_ : hasCoproducts ′ 𝒞 ′ }} where
-- {{_ : FiniteCoproductCategory 𝑖 on 𝒞}} where

  𝒞' : Category _
  𝒞' = ′ 𝒞 ′

  map-⊔ : ∀{a b c d : 𝒞} -> (a ⟶ b) × (c ⟶ d) -> (a ⊔ c ⟶ b ⊔ d)
  map-⊔ (f , g) = ⦗ f ◆ ι₀ , g ◆ ι₁ ⦘

  private instance
    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:⦗⦘

  -- private
  --   lem-1 : ∀{a b : 𝒞} -> map-⊔ (id {a = a} , id {a = b}) ∼ id
  --   lem-1 {a} {b} = P
  --     where
  --       ida : a ⟶ a
  --       ida = id

  --       idb : b ⟶ b
  --       idb = id

  --       idab : (a ⊓ b) ⟶ (a ⊓ b)
  --       idab = id

  --       P = ⧼ π₀ ◆ ida , π₁ ◆ idb ⧽    ⟨ cong-∼ (unit-r-◆ ∙ unit-l-◆ ⁻¹ , unit-r-◆ ∙ unit-l-◆ ⁻¹) ⟩-∼
  --           ⧼ idab ◆ π₀ , idab ◆ π₁ ⧽  ⟨ expand-⊓ ⁻¹ ⟩-∼
  --           idab                       ∎

  instance
    isSetoidHom:map-⊔ : ∀{a b c d : 𝒞} -> isSetoidHom ′((a ⟶ b) ×-𝒰 (c ⟶ d))′ (a ⊔ c ⟶ b ⊔ d) (map-⊔)
    isSetoidHom:map-⊔ = {!!}

  -- instance
  isFunctor:⊔ : isFunctor (𝒞' ×-𝐂𝐚𝐭 𝒞') 𝒞' (λ₋ _⊔_)
  isFunctor.map isFunctor:⊔               = map-⊔
  isFunctor.isSetoidHom:map isFunctor:⊔   = isSetoidHom:map-⊔
  -- {!!} -- record { cong-∼ = λ (p , q) → cong-∼ (refl ◈ p , refl ◈ q) }
  isFunctor.functoriality-id isFunctor:⊔  = {!!} -- lem-1
  isFunctor.functoriality-◆ isFunctor:⊔   = {!!}

  --------------------------------------------------------------
  -- properties

  module _ {a b c d : 𝒞} {f : a ⟶ b} {g : c ⟶ d} where
    module _ {{_ : isEpi f}} {{_ : isEpi g}} where
      isEpi:map-⊔ : isEpi (map-⊔ (f , g))
      isEpi.cancel-epi isEpi:map-⊔ {α = α} {β} p =
        let
          lem-1 : ι₀ ◆ α ∼ ι₀ ◆ β
          lem-1 = p
               ⟪ (refl ◈_) ⟫
               >> ι₀ ◆ (map-⊔ (f , g) ◆ α) ∼ ι₀ ◆ (map-⊔ (f , g) ◆ β) <<
               ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
               >> (ι₀ ◆ map-⊔ (f , g)) ◆ α ∼ (ι₀ ◆ map-⊔ (f , g)) ◆ β <<
               ⟪ reduce-ι₀ ◈ refl ≀∼≀ reduce-ι₀ ◈ refl ⟫
               >> (f ◆ ι₀) ◆ α ∼ (f ◆ ι₀) ◆ β <<
               ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
               >> f ◆ (ι₀ ◆ α) ∼ f ◆ (ι₀ ◆ β) <<
               ⟪ cancel-epi ⟫

          lem-2 : ι₁ ◆ α ∼ ι₁ ◆ β
          lem-2 = p
               ⟪ (refl ◈_) ⟫
               >> ι₁ ◆ (map-⊔ (f , g) ◆ α) ∼ ι₁ ◆ (map-⊔ (f , g) ◆ β) <<
               ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
               >> (ι₁ ◆ map-⊔ (f , g)) ◆ α ∼ (ι₁ ◆ map-⊔ (f , g)) ◆ β <<
               ⟪ reduce-ι₁ ◈ refl ≀∼≀ reduce-ι₁ ◈ refl ⟫
               >> (g ◆ ι₁) ◆ α ∼ (g ◆ ι₁) ◆ β <<
               ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
               >> g ◆ (ι₁ ◆ α) ∼ g ◆ (ι₁ ◆ β) <<
               ⟪ cancel-epi ⟫

          lem-3 : α ∼ β
          lem-3 = (lem-1 , lem-2)
                  ⟪ cong-∼ {{isSetoidHom:⦗⦘}} ⟫
                  >> ⦗ ι₀ ◆ α , ι₁ ◆ α ⦘ ∼ ⦗ ι₀ ◆ β , ι₁ ◆ β ⦘ <<
                  ⟪ expand-ι₀,ι₁ ⁻¹ ≀∼≀ expand-ι₀,ι₁ ⁻¹ ⟫

        in lem-3

