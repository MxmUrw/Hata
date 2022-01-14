
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.MetaVarReduction where


open import Verification.Conventions hiding (ℕ ; _⊔_ ; Σ)


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports

open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties


-----------------------------------------
-- Definition

module _ {𝒯 : 𝒰 𝑖} {{_ : isℒHMTypeCtx {𝑗} 𝒯}} where

  private
    Σ : ℒHMSignature _
    Σ = ′ 𝒯 ′

  -- [Definition]
  -- | We define an /abstraction of metavariables/.
  record isAbstr {k} {Q : ℒHMQuant Σ k} (κs : ℒHMTypes Σ) {μs₀ μs₁} (Γ₀ : ℒHMCtx Q μs₀) (Γ₁ : ℒHMCtx Q μs₁)
                (τ₀ : ℒHMType Σ μs₀) (τ₁ : ℒHMType Σ (μs₁ ⊔ κs)) : 𝒰 (𝑖 ､ 𝑗) where
    constructor isAbstr:byDef
    field metasProof : μs₀ ≅ (μs₁ ⊔ κs)
    field ctxProof : Γ₀ ⇃[ ⟨ metasProof ⟩ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
    field typeProof : τ₀ ⇃[ ⟨ metasProof ⟩ ]⇂ ≡ τ₁

  open isAbstr public
  -- //

  -- [Hide]
  module §-isAbstr where
    -- prop-1 : ∀{k} {Q : ℒHMQuant k} {κs : ℒHMTypes} {μs₀ μs₁ μs₂} {Γ₀ : ℒHMCtx Q μs₀} {Γ₁ : ℒHMCtx Q μs₁}
    --              {τ₀ : ℒHMType ⟨ μs₀ ⟩} {τ₁ : ℒHMType ⟨ μs₁ ⊔ κs ⟩}
    --          -> (σ₁₂ : μs₁ ⟶ μs₂)
    --          -> isAbstr κs Γ₀ Γ₁ τ₀ τ₁
    --          -> isAbstr κs Γ₀ (Γ₁ ⇃[ σ₁₂ ]⇂ᶜ) τ₀ (τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂)
    -- prop-1 = {!!}

    inverseCtxProof : ∀{k} {Q : ℒHMQuant Σ k} {κs : ℒHMTypes Σ} {μs₀ μs₁} {Γ₀ : ℒHMCtx Q μs₀} {Γ₁ : ℒHMCtx Q μs₁}
                  -> {τ₀ : ℒHMType Σ μs₀} {τ₁ : ℒHMType Σ (μs₁ ⊔ κs)}
                -> (A : isAbstr κs Γ₀ Γ₁ τ₀ τ₁)
                -> Γ₀ ≡ Γ₁ ⇃[ ι₀ ◆ ⟨ metasProof A ⟩⁻¹ ]⇂ᶜ
    inverseCtxProof {Γ₀ = Γ₀} {Γ₁} A =
      let ϕ = metasProof A
      in Γ₀                              ⟨ sym-Path functoriality-id-⇃[]⇂ᶜ ⟩-≡
        Γ₀ ⇃[ id ]⇂ᶜ                    ⟨ Γ₀ ⇃[≀ (inv-r-◆ (of ϕ)) ⁻¹ ≀]⇂ᶜ ⟩-≡
        Γ₀ ⇃[ ⟨ ϕ ⟩ ◆ ⟨ ϕ ⟩⁻¹ ]⇂ᶜ       ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₀}) ⟩-≡
        Γ₀ ⇃[ ⟨ ϕ ⟩ ]⇂ᶜ ⇃[ ⟨ ϕ ⟩⁻¹ ]⇂ᶜ  ⟨ cong _⇃[ ⟨ ϕ ⟩⁻¹ ]⇂ᶜ (ctxProof A) ⟩-≡
        Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ⟨ ϕ ⟩⁻¹ ]⇂ᶜ     ⟨ (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₁}) ⟩-≡
        Γ₁ ⇃[ ι₀ ◆ ⟨ ϕ ⟩⁻¹ ]⇂ᶜ ∎-≡

  -- //


