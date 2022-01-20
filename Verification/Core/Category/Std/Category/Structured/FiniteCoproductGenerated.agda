
module Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
-- open import Verification.Core.Data.Indexed.Duplicate
-- open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.Indexed.Instance.Monoid
-- open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Data.List.Variant.Binary.Natural


-------------------------
-- Finite coproducts via category of functors

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where

  ⨆ᶠᵘ : ∀{n : 人ℕ} -> 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞 -> ⟨ 𝒞 ⟩
  ⨆ᶠᵘ {incl x}   d = ⟨ d ⟩ (member incl)
  ⨆ᶠᵘ {a ⋆-⧜ b}  d = ⨆ᶠᵘ (leftᶠ ◆-𝐂𝐚𝐭 d) ⊔ ⨆ᶠᵘ (rightᶠ ◆-𝐂𝐚𝐭 d)
  ⨆ᶠᵘ {◌-⧜}      d = ⊥

  module _ {n : 人ℕ} where
    macro ⨆ᶠ = #structureOn (⨆ᶠᵘ {n})

  ∼-⨆ᶠ:byPointwise : ∀{n : 人ℕ} -> {F G : 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞} -> (∀(i : [ n ]ᶠ) -> ⟨ F ⟩ i ≅ ⟨ G ⟩ i) -> ⨆ᶠ F ≅ ⨆ᶠ G
  ∼-⨆ᶠ:byPointwise = {!!}

  module _ {n : 人ℕ} {F G : 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞} where
    ⨆ᶠ≀ : (F ∼ G) -> ⨆ᶠ F ≅ ⨆ᶠ G
    ⨆ᶠ≀ = {!!}









record isFiniteCoproductGenerated (𝒞 : FiniteCoproductCategory 𝑖) : 𝒰 𝑖 where
  -- constructor isFiniteCoproductGenerated:byDefinition
  field fcgSize : ⟨ 𝒞 ⟩ -> 人ℕ
  field fcg : (a : ⟨ 𝒞 ⟩) -> 𝐅𝐮𝐧𝐜 [ fcgSize a ]ᶠ (↳ 𝒞)
  field fcgIso : ∀ (a : ⟨ 𝒞 ⟩) -> a ≅ ⨆ᶠ (fcg a)

-- open isFiniteCoproductGenerated {{...}} public



