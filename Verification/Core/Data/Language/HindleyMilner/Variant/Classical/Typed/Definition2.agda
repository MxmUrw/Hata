
{-# OPTIONS --experimental-lossy-unification #-}

module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2 where

open import Verification.Conventions hiding (ℕ ; _⊔_ ; Σ)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.MetaVarReduction
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition


module _ {𝒯 : 𝒰 𝑖} {{_ : isℒHMTypeCtx {𝑗} 𝒯}} where

  private
    Σ : ℒHMSignature _
    Σ = ′ 𝒯 ′


  module §2-isTypedℒHM where

    prop-1 : ∀{k μs te} {Q R : ℒHMQuant Σ k} {Γ : ℒHMCtx Q μs} {τ : ℒHMType Σ μs}
          -> (σs : ℒHMQuantMap μs Q R)
          -> isTypedℒHM (μs ⊩ (apply-ℒHMQuantMap σs Γ) ⊢ τ) te
          -> isTypedℒHM (μs ⊩ (Γ) ⊢ τ) te
    prop-1 {μs = μs} {Q = Q} {R} {Γ} σs (var k∍i ψ {α} p) = var k∍i ϕ lem-5
      where
        ϕ : lookup-Listᴰ Q k∍i ⟶ μs
        ϕ = lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘

        lem-3 : ⦗ id , lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘ ⦘ ∼ ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ◆ ⦗ id , ψ ⦘
        lem-3 = ⦗ id , lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘ ⦘                  ⟨ cong-∼ {{isSetoidHom:⦗⦘}} ((reduce-ι₀ ⁻¹) , refl) ⟩-∼
                ⦗ ι₀ ◆ ⦗ id , ψ ⦘ , lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘ ⦘     ⟨ append-⦗⦘ ⁻¹ ⟩-∼
                ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ◆ ⦗ id , ψ ⦘    ∎

        lem-4 : lookup-Listᴰ² Γ k∍i ⇃[ ⦗ id , ϕ ⦘ ]⇂
                ≡ lookup-Listᴰ² (apply-ℒHMQuantMap σs Γ) k∍i ⇃[ ⦗ id , ψ ⦘ ]⇂
        lem-4 = lookup-Listᴰ² Γ k∍i ⇃[ ⦗ id , ϕ ⦘ ]⇂    ⟨ lookup-Listᴰ² Γ k∍i ⇃[≀ lem-3 ≀]⇂ ⟩-≡
                lookup-Listᴰ² Γ k∍i ⇃[ ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ◆ ⦗ id , ψ ⦘ ]⇂

                ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = lookup-Listᴰ² Γ k∍i} {f = ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘} {g = ⦗ id , ψ ⦘}) ⟩-≡

                lookup-Listᴰ² Γ k∍i ⇃[ ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ]⇂ ⇃[ ⦗ id , ψ ⦘ ]⇂    ⟨ cong _⇃[ ⦗ id , ψ ⦘ ]⇂ (§-ℒHMQuantMap.prop-2 σs Γ k∍i) ⟩-≡
                lookup-Listᴰ² (apply-ℒHMQuantMap σs Γ) k∍i                  ⇃[ ⦗ id , ψ ⦘ ]⇂      ∎-≡

        lem-5 : lookup-Listᴰ² Γ k∍i ⇃[ ⦗ id , ϕ ⦘ ]⇂ ≡ α
        lem-5 = trans-Path lem-4 p


    prop-1 σs (app p q) = app (prop-1 σs p) (prop-1 σs q)
    prop-1 {μs = μs} {Γ = Γ} σs (lam {α = α} p) =
      let lem-1 : α ≡ α ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂
          lem-1 = α                     ⟨ sym-Path functoriality-id-⇃[]⇂ ⟩-≡
                  α ⇃[ id ]⇂            ⟨ α ⇃[≀ §-ℒHMTypes.prop-1 ≀]⇂ ⟩-≡
                  α ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂   ∎-≡
      in p
        ⟪ transp-isTypedℒHM ((λ i -> lem-1 i ∷ apply-ℒHMQuantMap σs Γ)) refl-≡ ⟫
        ⟪ (prop-1 {Γ = α ∷ Γ} (ι₁ ∷ σs)) ⟫
        ⟪ lam ⟫
    prop-1 {μs = μs} {Q = Q} {R} {Γ = Γ} {τ = τ} σs (slet {μs = μs₁} {κs = κs} {Γ = Γ₁} {α = α} {α' = α'} isAb@(isAbstr:byDef σ pΓ pτ) p q) =
      slet (isAbstr:byDef σ lem-10 pτ) (prop-1 σs' lem-2) (prop-1 {Γ = α' ∷ Γ} (ι₁ ∷ σs) lem-5)
      where
        ϕ = ι₀ ◆ ⟨ σ ⟩⁻¹
        σs' = extend-ℒHMQuantMap (ϕ) σs

        lem-1 : Γ₁ ≡ apply-ℒHMQuantMap σs' (Γ ⇃[ ϕ ]⇂ᶜ)
        lem-1 = Γ₁                                    ⟨ §-isAbstr.inverseCtxProof isAb ⟩-≡
                apply-ℒHMQuantMap σs Γ ⇃[ ϕ ]⇂ᶜ       ⟨ sym-Path (§-ℒHMQuantMap.prop-1 ϕ σs Γ) ⟩-≡
                apply-ℒHMQuantMap σs' (Γ ⇃[ ϕ ]⇂ᶜ)    ∎-≡

        lem-2 : isTypedℒHM (μs₁ ⊩ apply-ℒHMQuantMap σs' (Γ ⇃[ ϕ ]⇂ᶜ) ⊢ α) _
        lem-2 = p
                ⟪ transp-isTypedℒHM lem-1 refl-≡ ⟫

        lem-4 : α' ≡ α' ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂
        lem-4 = α'                   ⟨ sym-Path functoriality-id-⇃[]⇂ ⟩-≡
                α' ⇃[ id ]⇂          ⟨ α' ⇃[≀ §-ℒHMTypes.prop-1 ≀]⇂ ⟩-≡
                α' ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂  ∎-≡

        lem-5 : isTypedℒHM (μs ⊩ ((α' ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂) ∷ apply-ℒHMQuantMap σs Γ) ⊢ τ) _
        lem-5 = q
                ⟪ transp-isTypedℒHM ((λ i -> lem-4 i ∷ apply-ℒHMQuantMap σs Γ)) refl-≡ ⟫

        lem-10 : Γ ⇃[ ϕ ]⇂ᶜ ⇃[ ⟨ σ ⟩ ]⇂ᶜ ≡ Γ ⇃[ ι₀ ]⇂ᶜ
        lem-10 = Γ ⇃[ ϕ ]⇂ᶜ ⇃[ ⟨ σ ⟩ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                Γ ⇃[ ϕ ◆ ⟨ σ ⟩ ]⇂ᶜ       ⟨ Γ ⇃[≀ assoc-l-◆ ≀]⇂ᶜ ⟩-≡
                Γ ⇃[ ι₀ ◆ (⟨ σ ⟩⁻¹ ◆ ⟨ σ ⟩) ]⇂ᶜ       ⟨ Γ ⇃[≀ refl ◈ inv-l-◆ (of σ) ≀]⇂ᶜ ⟩-≡
                Γ ⇃[ ι₀ ◆ id ]⇂ᶜ                     ⟨ Γ ⇃[≀ unit-r-◆ ≀]⇂ᶜ ⟩-≡
                Γ ⇃[ ι₀ ]⇂ᶜ                          ∎-≡

    prop-2 : ∀{k μs νs₀ νs₁ te} {Q : ℒHMQuant Σ k} {Γ : ℒHMCtx Q μs} {τ : ℒHMType Σ μs}
          -- -> (σs : ℒHMQuantMap μs Q R)
          -> {α : ℒHMType Σ (μs ⊔ νs₀)}
          -> (σ : νs₀ ⟶ μs ⊔ νs₁)
          -> isTypedℒHM (μs ⊩ (α ⇃[ ⦗ ι₀ , σ ⦘ ]⇂ ∷' Γ) ⊢ τ) te
          -> isTypedℒHM (μs ⊩ (α ∷ Γ) ⊢ τ) te
    prop-2 {μs = μs} {νs₀} {νs₁} {te} {Q = Q} {Γ = Γ} {τ = τ} {α = α} σ p =
      let σs : ℒHMQuantMap μs (νs₀ ∷' Q) (νs₁ ∷ Q)
          σs = σ ∷ id-ℒHMQuant
          lem-1 : isTypedℒHM (μs ⊩ (apply-ℒHMQuantMap σs (α ∷ Γ)) ⊢ τ) te
          lem-1 = p
                ⟪ transp-isTypedℒHM (λ i -> α ⇃[ ⦗ ι₀ , σ ⦘ ]⇂ ∷ §-ℒHMQuantMap.prop-3 {Γ = Γ} (~ i)) refl-≡ ⟫

      in prop-1 σs lem-1


