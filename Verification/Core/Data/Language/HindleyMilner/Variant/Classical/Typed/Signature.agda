
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature where


open import Verification.Conventions hiding (ℕ ; _⊔_)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
-- open import Verification.Core.Data.Language.HindleyMilner.Helpers
-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.MetaVarReduction



record isℒHMTypeCtx {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} (𝒯 : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  field {{isCategory:ℒHMTypeCtx}} : isCategory {𝑖} 𝒯
  field {{hasCoproducts:ℒHMTypeCtx}} : hasFiniteCoproducts ′ 𝒯 ′
  field {{hasUnification:ℒHMTypeCtx}} : hasUnification ′ 𝒯 ′
  field {{hasSplitEpiMonoFactorization:ℒHMTypeCtx}} : hasSplitEpiMonoFactorization ′ 𝒯 ′
  field ∼→≡ : ∀{a b : 𝒯} -> {f g : a ⟶ b} -> f ∼ g -> f ≡ g

  -- The main kind
  field μκᵘ : 𝒯

  -- The constructors
  field _⇒ᵘ_ : ∀{αs βs : 𝒯} -> (αs ⟶ βs) -> (αs ⟶ βs) -> αs ⟶ βs

  -- We need at least one constant
  field oneConstant : ∀{αs : 𝒯} -> αs ⟶ ⊥

open isℒHMTypeCtx {{...}} public

module _ (𝑖 : 𝔏 ^ 3) where
  ℒHMSignature = _ :& (isℒHMTypeCtx {𝑖 ⌄ 1 ⋯ 2} {𝑖 ⌄ 0})


module _ (Σ : ℒHMSignature 𝑖) where
  ℒHMTypeCtx = ⟨ Σ ⟩


module _ {𝒯 : 𝒰 𝑖} {{Σ : isℒHMTypeCtx {𝑗} 𝒯}} where
  μκ : 𝒯
  μκ = μκᵘ {{Σ}}

  infixr 30 _⇒_
  _⇒_ : ∀{αs βs : 𝒯} -> (αs ⟶ βs) -> (αs ⟶ βs) -> αs ⟶ βs
  _⇒_ = _⇒ᵘ_ {{Σ}}


{-
record ℒHMSignature (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  field ℒHMTypeCtx : 𝒰 (𝑖 ⌄ 0)
  field {{isCategory:ℒHMTypeCtx}} : isCategory {𝑖 ⌄ 1 ⋯ 2} ℒHMTypeCtx
  field {{hasCoproducts:ℒHMTypeCtx}} : hasCoproducts ′ ℒHMTypeCtx ′
  -- field ℒHM𝐓𝐲𝐩𝐞 : Category 𝑖

  -- The main kind
  field μκ : ℒHMTypeCtx

  -- The constructors
  field _⇒ᵘ_ : ∀{αs βs : ℒHMTypeCtx} -> (αs ⟶ βs) -> (αs ⟶ βs) -> αs ⟶ βs

open ℒHMSignature public

module _ {Σ : ℒHMSignature 𝑖} where
  _⇒_ : ∀{αs βs : ℒHMTypeCtx Σ} -> (αs ⟶ βs) -> (αs ⟶ βs) -> αs ⟶ βs
  _⇒_ = _⇒ᵘ_ Σ

-}
-- open ℒHMSignature          using (ℒHMTypeCtx) public
-- open ℒHMSignature {{...}} hiding (ℒHMTypeCtx) public





