
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement where

open import Verification.Conventions hiding (ℕ ; _⊔_)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition



record TypeAssignment {μs k} {Q : ℒHMQuant k} (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _/_⊩_,_,_,_
  field metas : ℒHMTypes
  field typeMetas : ℒHMTypes
  field ctx : ℒHMCtx Q (metas) --  ⊔ typeMetas)
  field typ : ℒHMType (⟨ metas ⊔ typeMetas ⟩)
  field isInstance : Γ <Γ ctx
  -- field hiddenEpiSub : μs ⟶ metas
  -- field hiddenEpiSubProof : hiddenEpiSub ◆ ι₀ ∼ (isInstance .fst)
  field hasType : isTypedℒHM (metas ⊔ typeMetas ⊩ (ctx ⇃[ ι₀ ]⇂ᶜ) ⊢ typ) te

open TypeAssignment public



module _ {μs k} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs} {te : UntypedℒHM k}  where
  record _<TI_ (𝑇 : TypeAssignment Γ te) (𝑆 : TypeAssignment Γ te) : 𝒰₀ where
    field tiSubₐ : metas 𝑇 ⟶ metas 𝑆
    field tiSubₓ : typeMetas 𝑇 ⟶ metas 𝑆 ⊔ typeMetas 𝑆
    field typProof : typ 𝑇 ⇃[ ⦗ tiSubₐ ◆ ι₀ , tiSubₓ ⦘ ]⇂ ≡ typ 𝑆
    field subProof : isInstance 𝑇 .fst ◆ tiSubₐ ∼ isInstance 𝑆 .fst

    ctxProofTI : ctx 𝑇 ⇃[ tiSubₐ ]⇂ᶜ ≡ ctx 𝑆
    ctxProofTI = ctx 𝑇 ⇃[ tiSubₐ ]⇂ᶜ  ⟨ cong _⇃[ tiSubₐ ]⇂ᶜ (sym-Path (isInstance 𝑇 .snd)) ⟩-≡
                 Γ ⇃[ fst (isInstance 𝑇) ]⇂ᶜ ⇃[ tiSubₐ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                 Γ ⇃[ fst (isInstance 𝑇) ◆ tiSubₐ ]⇂ᶜ  ⟨ Γ ⇃[≀ subProof ≀]⇂ᶜ ⟩-≡
                 Γ ⇃[ fst (isInstance 𝑆) ]⇂ᶜ           ⟨ isInstance 𝑆 .snd ⟩-≡
                 ctx 𝑆 ∎-≡

  open _<TI_ public


PrincipalTypeAssignment : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) -> 𝒰₀
PrincipalTypeAssignment Γ te = ∑ λ (𝑇 : TypeAssignment Γ te) -> ∀(𝑆 : TypeAssignment Γ te) -> 𝑇 <TI 𝑆

TypingDecision : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) -> 𝒰₀
TypingDecision Γ te = (TypeAssignment Γ te -> ⊥-𝒰 {ℓ₀}) + (PrincipalTypeAssignment Γ te)



