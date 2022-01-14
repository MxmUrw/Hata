
{-# OPTIONS --experimental-lossy-unification #-}
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.CategoricalProperties where

open import Verification.Conventions hiding (ℕ ; _⊔_ ; Σ)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature


-- testing
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary using (reduce-ι₀ ; reduce-ι₁)
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition

-- [Hide]


--------------------------------------
-- NOTE
-- This is code copied from:
--   module Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal where
-- It is unclear why instantiation does
-- not work here.

-------------
-- BEGIN DUPLICATE CODE

{-
open import Verification.Conventions hiding (_⊔_)

byExpand-ι₀,ι₁ : ∀{a b c : ℒHMTypes} -> {f g : a ⊔ b ⟶ c}
                  -> ι₀ ◆ f ∼ ι₀ ◆ g
                  -> ι₁ ◆ f ∼ ι₁ ◆ g
                  -> f ∼ g
byExpand-ι₀,ι₁ {f = f} {g} p₀ p₁ =
  f                   ⟨ expand-ι₀,ι₁ ⟩-∼
  ⦗ ι₀ ◆ f , ι₁ ◆ f ⦘ ⟨ ⦗≀ p₀ , p₁ ≀⦘ ⟩-∼
  ⦗ ι₀ ◆ g , ι₁ ◆ g ⦘ ⟨ expand-ι₀,ι₁ ⁻¹ ⟩-∼
  g                   ∎

module assoc-l-⊔' {a b c : ℒHMTypes} where

  f : (a ⊔ b) ⊔ c ⟶ a ⊔ (b ⊔ c)
  f = ⦗ ⦗ ι₀ , ι₀ ◆ ι₁ ⦘ , ι₁ ◆ ι₁ ⦘

  g : a ⊔ (b ⊔ c) ⟶ (a ⊔ b) ⊔ c
  g = ⦗ ι₀ ◆ ι₀ , ⦗ ι₁ ◆ ι₀ , ι₁ ⦘ ⦘

  abstract
    lem-1a : ι₀ ◆ (ι₀ ◆ (f ◆ g)) ∼ ι₀ ◆ (ι₀ ◆ id)
    lem-1a = ι₀ ◆ (ι₀ ◆ (f ◆ g))   ⟨ refl ◈ assoc-r-◆ ⟩-∼
              ι₀ ◆ ((ι₀ ◆ f) ◆ g)   ⟨ refl ◈ (reduce-ι₀ ◈ refl) ⟩-∼
              ι₀ ◆ (_ ◆ g)          ⟨ assoc-r-◆ ⟩-∼
              (ι₀ ◆ _) ◆ g          ⟨ reduce-ι₀ ◈ refl ⟩-∼
              ι₀ ◆ g                ⟨ reduce-ι₀ ⟩-∼
              ι₀ ◆ ι₀               ⟨ refl ◈ unit-r-◆ ⁻¹ ⟩-∼
              ι₀ ◆ (ι₀ ◆ id)        ∎
-}
{-
  abstract
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

  abstract
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

  Proof : (a ⊔ b) ⊔ c ≅ a ⊔ (b ⊔ c)
  Proof = f since record { inverse-◆ = g ; inv-r-◆ = lem-1 ; inv-l-◆ = lem-2 }


module §-assoc-l-⊔' where
  prop-1 : ∀{a b c : ℒHMTypes} -> (ι₀ ◆ ι₀) ◆ ⟨ assoc-l-⊔'.Proof {a = a} {b} {c} ⟩ ∼ ι₀
  prop-1 = (ι₀ ◆ ι₀) ◆ _  ⟨ assoc-l-◆ ⟩-∼
            ι₀ ◆ (ι₀ ◆ _)  ⟨ refl ◈ reduce-ι₀ ⟩-∼
            ι₀ ◆ _         ⟨ reduce-ι₀ ⟩-∼
            ι₀             ∎

  prop-1' : ∀{a b c : ℒHMTypes} -> (ι₀ ◆ ι₀) ∼ ι₀ ◆ ⟨ assoc-l-⊔'.Proof {a = a} {b} {c} ⟩⁻¹
  prop-1' = switch-≅-r {f = ι₀ ◆ ι₀} {ψ = assoc-l-⊔'.Proof} {g = ι₀} prop-1

  prop-2 : ∀{a b c x : ℒHMTypes}
           -> {f : a ⟶ x} {g : b ⟶ x} {h : c ⟶ x}
           -> ⦗ f , ⦗ g , h ⦘ ⦘ ∼ ⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘
  prop-2 {f = f} {g} {h} = byExpand-ι₀,ι₁ lem-1 (byExpand-ι₀,ι₁ lem-2 lem-3)
    where
      lem-1 : ι₀ ◆ ⦗ f , ⦗ g , h ⦘ ⦘ ∼ ι₀ ◆ (⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘)
      lem-1 = ι₀ ◆ ⦗ f , ⦗ g , h ⦘ ⦘   ⟨ reduce-ι₀ ⟩-∼
              f                                                   ⟨ reduce-ι₀ ⁻¹ ⟩-∼
              ι₀ ◆ ⦗ f , g ⦘                                      ⟨ refl ◈ reduce-ι₀ ⁻¹ ⟩-∼
              ι₀ ◆ (ι₀ ◆ ⦗ ⦗ f , g ⦘ , h ⦘)                       ⟨ assoc-r-◆ ⟩-∼
              (ι₀ ◆ ι₀) ◆ ⦗ ⦗ f , g ⦘ , h ⦘                       ⟨ reduce-ι₀ ⁻¹ ◈ refl ⟩-∼
              (ι₀ ◆ ⟨ assoc-l-⊔'.Proof ⟩⁻¹) ◆ ⦗ ⦗ f , g ⦘ , h ⦘   ⟨ assoc-l-◆ ⟩-∼
              ι₀ ◆ (⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘)   ∎

      lem-2 : ι₀ ◆ (ι₁ ◆ ⦗ f , ⦗ g , h ⦘ ⦘) ∼ ι₀ ◆ (ι₁ ◆ (⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘))
      lem-2 = ι₀ ◆ (ι₁ ◆ ⦗ f , ⦗ g , h ⦘ ⦘)   ⟨ refl ◈ reduce-ι₁ ⟩-∼
              ι₀ ◆ ⦗ g , h ⦘   ⟨ reduce-ι₀ ⟩-∼
              g   ⟨ reduce-ι₁ ⁻¹ ⟩-∼
              ι₁ ◆ ⦗ f , g ⦘   ⟨ refl ◈ reduce-ι₀ ⁻¹ ⟩-∼
              ι₁ ◆ (ι₀ ◆ ⦗ ⦗ f , g ⦘ , h ⦘)   ⟨ assoc-r-◆ ⟩-∼
              (ι₁ ◆ ι₀) ◆ ⦗ ⦗ f , g ⦘ , h ⦘   ⟨ reduce-ι₀ ⁻¹ ◈ refl ⟩-∼
              (ι₀ ◆ _) ◆ ⦗ ⦗ f , g ⦘ , h ⦘   ⟨ assoc-l-◆ ⟩-∼
              ι₀ ◆ (_ ◆ ⦗ ⦗ f , g ⦘ , h ⦘)   ⟨ refl ◈ (reduce-ι₁ ⁻¹ ◈ refl) ⟩-∼
              ι₀ ◆ ((ι₁ ◆ _) ◆ ⦗ ⦗ f , g ⦘ , h ⦘)   ⟨ refl ◈ assoc-l-◆ ⟩-∼
              ι₀ ◆ (ι₁ ◆ (⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘))   ∎

      lem-3 : ι₁ ◆ (ι₁ ◆ ⦗ f , ⦗ g , h ⦘ ⦘) ∼ ι₁ ◆ (ι₁ ◆ (⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘))
      lem-3 = ι₁ ◆ (ι₁ ◆ ⦗ f , ⦗ g , h ⦘ ⦘)   ⟨ refl ◈ reduce-ι₁ ⟩-∼
              ι₁ ◆ ⦗ g , h ⦘   ⟨ reduce-ι₁ ⟩-∼
              h   ⟨ reduce-ι₁ ⁻¹ ⟩-∼
              (ι₁) ◆ ⦗ ⦗ f , g ⦘ , h ⦘   ⟨ reduce-ι₁ ⁻¹ ◈ refl ⟩-∼
              (ι₁ ◆ _) ◆ ⦗ ⦗ f , g ⦘ , h ⦘   ⟨ assoc-l-◆ ⟩-∼
              ι₁ ◆ (_ ◆ ⦗ ⦗ f , g ⦘ , h ⦘)   ⟨ refl ◈ (reduce-ι₁ ⁻¹ ◈ refl) ⟩-∼
              ι₁ ◆ ((ι₁ ◆ _) ◆ ⦗ ⦗ f , g ⦘ , h ⦘)   ⟨ refl ◈ assoc-l-◆ ⟩-∼
              ι₁ ◆ (ι₁ ◆ (⟨ assoc-l-⊔'.Proof ⟩⁻¹ ◆ ⦗ ⦗ f , g ⦘ , h ⦘))   ∎

-}

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal



module _ {𝒯 : 𝒰 𝑖} {{_ : isℒHMTypeCtx {𝑗} 𝒯}} where

  private
    Σ : ℒHMSignature _
    Σ = ′ 𝒯 ′

  assoc-l-⊔-ℒHMTypes : ∀{a b c : ℒHMTypes Σ} -> (a ⊔ b) ⊔ c ≅ a ⊔ (b ⊔ c)
  assoc-l-⊔-ℒHMTypes {a} {b} {c} = assoc-l-⊔

-- END DUPLICATE CODE
-------------

---------------------------
-- other categorical proofs

  module §-ℒHMTypes where
    prop-1 : ∀{a b : ℒHMTypes Σ} -> id {a = a ⊔ b} ∼ ⦗ ι₀ , ι₁ ⦘
    prop-1 {a} {b} = {!!}
      -- id {a = a ⊔ b}                    ⟨ expand-ι₀,ι₁ ⟩-∼
      -- ⦗ ι₀ ◆ id , ι₁ ◆ id ⦘ ⟨ ⦗≀ unit-r-◆ , unit-r-◆ ≀⦘ ⟩-∼
      -- ⦗ ι₀ , ι₁ ⦘           ∎



-- //
