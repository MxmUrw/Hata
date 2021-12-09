
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Proofs where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition


module §-HM-Proofs where

  module _ {μs : ℒHMTypes}
           {μs₂ : ℒHMTypes}
           (α₂ : ℒHMType ⟨ μs₂ ⊔ ⊥ ⟩)
           (σ₀₂ : μs ⊔ st ⟶ μs₂) where
    private
      αᵘ : ℒHMType ⟨ st ⟩
      αᵘ = var incl

      α₀ : ℒHMType ⟨ (μs ⊔ st) ⊔ ⊥ ⟩
      α₀ = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂

      lem-1 : (ι₁ ◆ ι₀) ◆ (σ₀₂ ⇃⊔⇂ id) ∼ ⧜subst (incl α₂)
      lem-1 =
            (ι₁ ◆ ι₀) ◆ (σ₀₂ ⇃⊔⇂ id)                  ⟨ assoc-l-◆ {f = ι₁} {ι₀} {σ₀₂ ⇃⊔⇂ id} ⟩-∼
            ι₁ ◆ (ι₀ ◆ (σ₀₂ ⇃⊔⇂ id))                  ⟨ {!!} ⟩-∼
            ι₁ ◆ (σ₀₂ ◆ ι₀)                           ⟨ {!!} ⟩-∼
            ⧜subst (incl α₂) ◆ ⦗ id , elim-⊥ ⦘ ◆ ι₀  ⟨ {!!} ⟩-∼
            ⧜subst (incl α₂)                          ∎

    prop-1 : α₀ ⇃[ σ₀₂ ⇃⊔⇂ id ]⇂ ≡ α₂
    prop-1 = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂ ⇃[ σ₀₂ ⇃⊔⇂ id ]⇂          ⟨ functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = ι₁ ◆ ι₀} {g = σ₀₂ ⇃⊔⇂ id} ⟩-≡
            αᵘ ⇃[ (ι₁ ◆ ι₀) ◆ (σ₀₂ ⇃⊔⇂ id)]⇂            ⟨ αᵘ ⇃[≀ lem-1 ≀]⇂ ⟩-≡
            αᵘ ⇃[ ⧜subst (incl α₂) ]⇂                   ⟨ refl-≡ ⟩-≡
            α₂                                          ∎-≡

  module _ {μs νs ξs : ℒHMTypes}
           (σ₀ : μs ⟶ ξs)
           (σ₁ : νs ⟶ ξs)
           {k} {Q : ℒHMQuant k}
           (Γ : ℒHMCtxFor Q μs) where

    prop-2 : Γ ⇃[ ι₀ ]⇂-CtxFor ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂-CtxFor ≡ Γ ⇃[ σ₀ ]⇂-CtxFor
    prop-2 = {!!}

  module _ {μs νs ξs : ℒHMTypes}
           (σ₀ : μs ⟶ ξs)
           (σ₁ : νs ⟶ ξs)
           (τ : ℒHMType ⟨ μs ⟩) where

    prop-3 : τ ⇃[ ι₀ ]⇂ ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂ ≡ τ ⇃[ σ₀ ]⇂
    prop-3 = {!!}

  module _ {μs νs ξs : ℒHMTypes}
           (σ₀ : νs ⟶ ξs)
           (σ₁ : μs ⟶ ξs)
           (τ : ℒHMType ⟨ μs ⟩) where

    prop-4 : τ ⇃[ ι₁ ]⇂ ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂ ≡ τ ⇃[ σ₁ ]⇂
    prop-4 = {!!}

