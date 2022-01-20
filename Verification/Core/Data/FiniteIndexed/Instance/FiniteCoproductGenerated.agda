
module Verification.Core.Data.FiniteIndexed.Instance.FiniteCoproductGenerated where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Discrete
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
-- open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Category.Construction.Coproduct

open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated



module §-eval-⋆ᶠ where
  module _ {as bs : 人ℕ} {𝒞 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒞}} {F : Functor ([ as ]ᶠ +-𝐂𝐚𝐭 [ bs ]ᶠ) 𝒞} where
    prop-1 : ⨆ᶠ (eval-⋆ᶠ ◆-𝐂𝐚𝐭 F) ≅ ⨆ᶠ (ι₀-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F) ⊔ ⨆ᶠ (ι₁-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F)
    prop-1 = ∼-⨆ᶠ:byPointwise {G = ι₀-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F} (λ i → refl-≅) ≀⊔≀ ∼-⨆ᶠ:byPointwise {G = ι₁-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F} (λ i → refl-≅)


module _ {I : 𝒰 𝑖} where
  private
    fcg'Size : ⋆List I -> 人ℕ
    fcg'Size x = map-⋆List (const tt) x

    fcg' : (a : ⋆List I) -> 𝐅𝐮𝐧𝐜 [ fcg'Size a ]ᶠ (𝐅𝐢𝐧𝐈𝐱 I)
    fcg' (incl x) = (λ _ → incl (incl x)) since isFunctor:byDiscrete
    fcg' (a ⋆-⧜ b) = eval-⋆ᶠ ◆-𝐂𝐚𝐭 ⦗ fcg' a , fcg' b ⦘-𝐂𝐚𝐭
    fcg' ◌-⧜ = (λ ()) since isFunctor:byDiscrete


    fcg'Iso : (a : ⋆List I) -> incl a ≅ ⨆ᶠ (fcg' a)
    fcg'Iso (incl x) = refl-≅
    fcg'Iso (a ⋆-⧜ b) =
         incl (a ⋆-⧜ b)

         ⟨  fcg'Iso a ≀⊔≀ fcg'Iso b ⟩-≅

         ⨆ᶠ (fcg' a) ⊔ ⨆ᶠ (fcg' b)

         ⟨ ⨆ᶠ≀ (sym-≅ reduce-ι₀-𝐂𝐚𝐭) ≀⊔≀ ⨆ᶠ≀ (sym-≅ reduce-ι₁-𝐂𝐚𝐭) ⟩-≅

         ⨆ᶠ (ι₀-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ⦗ fcg' a , fcg' b ⦘-𝐂𝐚𝐭) ⊔ ⨆ᶠ (ι₁-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ⦗ fcg' a , fcg' b ⦘-𝐂𝐚𝐭)

         ⟨ sym-≅ (§-eval-⋆ᶠ.prop-1) ⟩-≅

         ⨆ᶠ (eval-⋆ᶠ ◆-𝐂𝐚𝐭 ⦗ fcg' a , fcg' b ⦘-𝐂𝐚𝐭)

         ⟨ refl-≅ ⟩-≅

         ⨆ᶠ (fcg' (a ⋆-⧜ b))

         ∎-≅

    fcg'Iso ◌-⧜ = refl-≅ -- refl-≅


  instance
    isFiniteCoproductGenerated:𝐅𝐢𝐧𝐈𝐱 : isFiniteCoproductGenerated (𝐅𝐢𝐧𝐈𝐱 I)
    isFiniteCoproductGenerated:𝐅𝐢𝐧𝐈𝐱 = record
      { fcgSize = λ x -> fcg'Size ⟨ x ⟩
      ; fcg = λ x -> fcg' ⟨ x ⟩
      ; fcgIso = λ x -> fcg'Iso ⟨ x ⟩
      }



