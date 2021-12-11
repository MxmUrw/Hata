
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition

open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition

open import Verification.Core.Order.Preorder



record CtxTypingInstance {μs k} {Q : ℒHMQuant k} (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _/_⊩_,_,_,_
  field metas : ℒHMTypes
  field typeMetas : ℒHMTypes
  field ctx : ℒHMCtx Q (metas) --  ⊔ typeMetas)
  field typ : ℒHMType (⟨ metas ⊔ typeMetas ⟩)
  field isInstance : Γ <Γ ctx
  -- field hiddenEpiSub : μs ⟶ metas
  -- field hiddenEpiSubProof : hiddenEpiSub ◆ ι₀ ∼ (isInstance .fst)
  field hasType : isTypedℒHM (metas ⊔ typeMetas ⊩ (ctx ⇃[ ι₀ ]⇂ᶜ) ⊢ typ) te

open CtxTypingInstance public



module _ {μs k} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs} {te : UntypedℒHM k}  where
  record _<TI_ (𝑇 : CtxTypingInstance Γ te) (𝑆 : CtxTypingInstance Γ te) : 𝒰₀ where
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


InitialCtxTypingInstance : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) -> 𝒰₀
InitialCtxTypingInstance Γ te = ∑ λ (𝑇 : CtxTypingInstance Γ te) -> ∀(𝑆 : CtxTypingInstance Γ te) -> 𝑇 <TI 𝑆

TypingDecision : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) -> 𝒰₀
TypingDecision Γ te = (CtxTypingInstance Γ te -> ⊥-𝒰 {ℓ₀}) + (InitialCtxTypingInstance Γ te)
