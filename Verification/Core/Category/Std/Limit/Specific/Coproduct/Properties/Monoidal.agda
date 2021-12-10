
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

-- {-# DISPLAY isCoequalizer.π₌ _ = π₌ #-}
{-# DISPLAY isCategory.Hom _ a b = a ⟶ b #-}
{-# DISPLAY isCategory.id _ = id #-}
{-# DISPLAY isCategory._◆_ _ f g = f ◆ g #-}
{-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
{-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY isCoproduct.⦗_⦘ _ x = ⦗ x ⦘ #-}


module _ {𝒞' : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞'}} where
  private
    macro 𝒞 = #structureOn ⟨ 𝒞' ⟩
    instance
      _ : isSetoid 𝒞
      _ = isSetoid:byCategory

  byExpand-ι₀,ι₁ : ∀{a b c : 𝒞} -> {f g : a ⊔ b ⟶ c}
                   -> ι₀ ◆ f ∼ ι₀ ◆ g
                   -> ι₁ ◆ f ∼ ι₁ ◆ g
                   -> f ∼ g
  byExpand-ι₀,ι₁ {f = f} {g} p₀ p₁ =
    f                   ⟨ expand-ι₀,ι₁ ⟩-∼
    ⦗ ι₀ ◆ f , ι₁ ◆ f ⦘ ⟨ ⦗≀ p₀ , p₁ ≀⦘ ⟩-∼
    ⦗ ι₀ ◆ g , ι₁ ◆ g ⦘ ⟨ expand-ι₀,ι₁ ⁻¹ ⟩-∼
    g                   ∎

  -- unit-l-⊔ : ∀{a : 𝒞} -> ⊥ ⊔ a ∼ a
  -- unit-l-⊔ {a} = {!!}
  --   where
  --     f : ⊥ ⊔ a ⟶ a
  --     f = ⦗ elim-⊥ , id ⦘

  --     g : a ⟶ ⊥ ⊔ a
  --     g = ι₁

  --     lem-1 : f ◆ g ∼ id
  --     lem-1 = ? -- ⦗ elim-⊥ , id ⦘ ◆ ι₁

  -- unit-r-⊔ : ∀{a : 𝒞} -> a ⊔ ⊥ ∼ a
  -- unit-r-⊔ = {!!}

  module assoc-l-⊔ {a b c : 𝒞} where

    f : (a ⊔ b) ⊔ c ⟶ a ⊔ (b ⊔ c)
    f = ⦗ ⦗ ι₀ , ι₀ ◆ ι₁ ⦘ , ι₁ ◆ ι₁ ⦘

    g : a ⊔ (b ⊔ c) ⟶ (a ⊔ b) ⊔ c
    g = ⦗ ι₀ ◆ ι₀ , ⦗ ι₁ ◆ ι₀ , ι₁ ⦘ ⦘

    lem-1a : ι₀ ◆ (ι₀ ◆ (f ◆ g)) ∼ ι₀ ◆ (ι₀ ◆ id)
    lem-1a = ι₀ ◆ (ι₀ ◆ (f ◆ g))   ⟨ refl ◈ assoc-r-◆ ⟩-∼
              ι₀ ◆ ((ι₀ ◆ f) ◆ g)   ⟨ refl ◈ (reduce-ι₀ ◈ refl) ⟩-∼
              ι₀ ◆ (_ ◆ g)          ⟨ assoc-r-◆ ⟩-∼
              (ι₀ ◆ _) ◆ g          ⟨ reduce-ι₀ ◈ refl ⟩-∼
              ι₀ ◆ g                ⟨ reduce-ι₀ ⟩-∼
              ι₀ ◆ ι₀               ⟨ refl ◈ unit-r-◆ ⁻¹ ⟩-∼
              ι₀ ◆ (ι₀ ◆ id)        ∎

    lem-1b : ι₁ ◆ (ι₀ ◆ (f ◆ g)) ∼ ι₁ ◆ (ι₀ ◆ id)
    lem-1b = ι₁ ◆ (ι₀ ◆ (f ◆ g))   ⟨ refl ◈ assoc-r-◆ ⟩-∼
              ι₁ ◆ ((ι₀ ◆ f) ◆ g)   ⟨ refl ◈ (reduce-ι₀ ◈ refl) ⟩-∼
              ι₁ ◆ (_ ◆ g)          ⟨ assoc-r-◆ ⟩-∼
              (ι₁ ◆ _) ◆ g          ⟨ reduce-ι₁ ◈ refl ⟩-∼
              (ι₀ ◆ ι₁) ◆ g         ⟨ assoc-l-◆ ⟩-∼
              ι₀ ◆ (ι₁ ◆ g)         ⟨ refl ◈ reduce-ι₁ ⟩-∼
              ι₀ ◆ _                ⟨ reduce-ι₀ ⟩-∼
              ι₁ ◆ ι₀               ⟨ refl ◈ unit-r-◆ ⁻¹ ⟩-∼
              ι₁ ◆ (ι₀ ◆ id)        ∎

    lem-1c : ι₁ ◆ (f ◆ g) ∼ ι₁ ◆ id
    lem-1c = ι₁ ◆ (f ◆ g)          ⟨ assoc-r-◆ ⟩-∼
              (ι₁ ◆ f) ◆ g          ⟨ reduce-ι₁ ◈ refl ⟩-∼
              (ι₁ ◆ ι₁) ◆ g         ⟨ assoc-l-◆ ⟩-∼
              ι₁ ◆ (ι₁ ◆ g)         ⟨ refl ◈ reduce-ι₁ ⟩-∼
              ι₁ ◆ _                ⟨ reduce-ι₁ ⟩-∼
              ι₁                    ⟨ unit-r-◆ ⁻¹ ⟩-∼
              ι₁ ◆ id               ∎

    lem-1 : f ◆ g ∼ id
    lem-1 = byExpand-ι₀,ι₁ (byExpand-ι₀,ι₁ lem-1a lem-1b) lem-1c

    lem-2a : ι₀ ◆ (g ◆ f) ∼ ι₀ ◆ id
    lem-2a = ι₀ ◆ (g ◆ f)          ⟨ assoc-r-◆ ⟩-∼
             (ι₀ ◆ g) ◆ f          ⟨ reduce-ι₀ ◈ refl ⟩-∼
             (ι₀ ◆ ι₀) ◆ f         ⟨ assoc-l-◆ ⟩-∼
             ι₀ ◆ (ι₀ ◆ f)         ⟨ refl ◈ reduce-ι₀ ⟩-∼
             ι₀ ◆ _                ⟨ reduce-ι₀ ⟩-∼
             ι₀                    ⟨ unit-r-◆ ⁻¹ ⟩-∼
             ι₀ ◆ id               ∎

    lem-2b : ι₀ ◆ (ι₁ ◆ (g ◆ f)) ∼ ι₀ ◆ (ι₁ ◆ id)
    lem-2b = ι₀ ◆ (ι₁ ◆ (g ◆ f))   ⟨ refl ◈ assoc-r-◆ ⟩-∼
             ι₀ ◆ ((ι₁ ◆ g) ◆ f)   ⟨ refl ◈ (reduce-ι₁ ◈ refl) ⟩-∼
             ι₀ ◆ (_ ◆ f)          ⟨ assoc-r-◆ ⟩-∼
             (ι₀ ◆ _) ◆ f          ⟨ reduce-ι₀ ◈ refl ⟩-∼
             (ι₁ ◆ ι₀) ◆ f         ⟨ assoc-l-◆ ⟩-∼
             ι₁ ◆ (ι₀ ◆ f)         ⟨ refl ◈ reduce-ι₀ ⟩-∼
             ι₁ ◆ _                ⟨ reduce-ι₁ ⟩-∼
             ι₀ ◆ ι₁               ⟨ refl ◈ unit-r-◆ ⁻¹ ⟩-∼
             ι₀ ◆ (ι₁ ◆ id)        ∎

    lem-2c : ι₁ ◆ (ι₁ ◆ (g ◆ f)) ∼ ι₁ ◆ (ι₁ ◆ id)
    lem-2c = ι₁ ◆ (ι₁ ◆ (g ◆ f))   ⟨ refl ◈ assoc-r-◆ ⟩-∼
             ι₁ ◆ ((ι₁ ◆ g) ◆ f)   ⟨ refl ◈ (reduce-ι₁ ◈ refl) ⟩-∼
             ι₁ ◆ (_ ◆ f)          ⟨ assoc-r-◆ ⟩-∼
             (ι₁ ◆ _) ◆ f          ⟨ reduce-ι₁ ◈ refl ⟩-∼
             ι₁ ◆ f                ⟨ reduce-ι₁ ⟩-∼
             ι₁ ◆ ι₁               ⟨ refl ◈ unit-r-◆ ⁻¹ ⟩-∼
             ι₁ ◆ (ι₁ ◆ id)        ∎

    lem-2 : g ◆ f ∼ id
    lem-2 = byExpand-ι₀,ι₁ lem-2a (byExpand-ι₀,ι₁ lem-2b lem-2c)

    Proof : (a ⊔ b) ⊔ c ∼ a ⊔ (b ⊔ c)
    Proof = f since record { inverse-◆ = g ; inv-r-◆ = lem-1 ; inv-l-◆ = lem-2 }

  assoc-l-⊔ : ∀{a b c : 𝒞} -> (a ⊔ b) ⊔ c ∼ a ⊔ (b ⊔ c)
  assoc-l-⊔ = assoc-l-⊔.Proof


  module §-assoc-l-⊔ where
    prop-1 : ∀{a b c : 𝒞} -> (ι₀ ◆ ι₀) ◆ ⟨ assoc-l-⊔ {a = a} {b} {c} ⟩ ∼ ι₀
    prop-1 = (ι₀ ◆ ι₀) ◆ _  ⟨ assoc-l-◆ ⟩-∼
             ι₀ ◆ (ι₀ ◆ _)  ⟨ refl ◈ reduce-ι₀ ⟩-∼
             ι₀ ◆ _         ⟨ reduce-ι₀ ⟩-∼
             ι₀             ∎


  -- isMonoid:byCoproduct : isMonoid 𝒞
  -- isMonoid:byCoproduct = record
  --                          { _⋆_ = _⊔_
  --                          ; ◌ = ⊥
  --                          ; unit-l-⋆ = {!!}
  --                          ; unit-r-⋆ = {!!}
  --                          ; assoc-l-⋆ = {!!}
  --                          ; _≀⋆≀_ = {!!}
  --                          }

