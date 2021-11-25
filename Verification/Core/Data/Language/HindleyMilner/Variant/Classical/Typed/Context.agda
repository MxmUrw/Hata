
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
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

open import Verification.Core.Order.Preorder



record _<Γ_ {k} {Q : ℒHMQuant k} {μs νs} (Γ : ℒHMCtxFor Q μs) (Γ' : ℒHMCtxFor Q νs) : 𝒰₀ where
  field fst : μs ⟶ νs
  field snd : Γ ⇃[ fst ]⇂-CtxFor ≡ Γ'
open _<Γ_ public

record SomeℒHMCtxᵘ {k} (Q : ℒHMQuant k) : 𝒰₀ where
  constructor _,_
  field fst : ℒHMTypes
  field snd : ℒHMCtxFor Q fst

open SomeℒHMCtxᵘ public


module _ {k} (Q : ℒHMQuant k) where
  macro SomeℒHMCtx = #structureOn (SomeℒHMCtxᵘ Q)


module _ {k} {Q : ℒHMQuant k} where

  instance
    isSetoid:SomeℒHMCtx : isSetoid (SomeℒHMCtx Q)
    isSetoid:SomeℒHMCtx = isSetoid:byPath

  -- showing that this gives a preorder
  _≤-SomeℒHMCtx_ : (SomeℒHMCtx Q) -> SomeℒHMCtx Q -> 𝒰₀
  _≤-SomeℒHMCtx_ (_ , Γ) (_ , Δ) = Γ <Γ Δ

  reflexive-SomeℒHMCtx : ∀{a} -> a ≤-SomeℒHMCtx a
  reflexive-SomeℒHMCtx = record
    { fst = id
    ; snd = functoriality-id-⇃[]⇂-CtxFor
    }

  _⟡-SomeℒHMCtx_ : ∀{a b c} -> a ≤-SomeℒHMCtx b -> b ≤-SomeℒHMCtx c -> a ≤-SomeℒHMCtx c
  _⟡-SomeℒHMCtx_ {a = _ , Γ₀} {_ , Γ₁} {_ , Γ₂} Γ₀<Γ₁ Γ₁<Γ₂ =
    let σ₀₁ = fst Γ₀<Γ₁
        σ₁₂ = fst Γ₁<Γ₂
        σ₀₂ = σ₀₁ ◆ σ₁₂

        lem-1 : Γ₀ ⇃[ σ₀₂ ]⇂-CtxFor ≡ Γ₂
        lem-1 = Γ₀ ⇃[ σ₀₁ ◆ σ₁₂ ]⇂-CtxFor      ⟨ sym-Path (functoriality-◆-⇃[]⇂-CtxFor) ⟩-≡
                Γ₀ ⇃[ σ₀₁ ]⇂-CtxFor ⇃[ σ₁₂ ]⇂-CtxFor ⟨ cong _⇃[ σ₁₂ ]⇂-CtxFor (snd Γ₀<Γ₁) ⟩-≡
                Γ₁  ⇃[ σ₁₂ ]⇂-CtxFor                 ⟨ snd Γ₁<Γ₂ ⟩-≡
                Γ₂                                  ∎-≡

    in record { fst = σ₀₂ ; snd = lem-1 }

  instance
    isPreorder:SomeℒHMCtx : isPreorder ℓ₀ (SomeℒHMCtx Q)
    isPreorder:SomeℒHMCtx = record
      { _≤_ = _≤-SomeℒHMCtx_
      ; reflexive = reflexive-SomeℒHMCtx
      ; _⟡_ = _⟡-SomeℒHMCtx_
      ; transp-≤ = {!!}
      }



  -----------------------------------------
  -- special functions
  -- tail-SomeℒHMCtx : ∀{as bs : SomeℒHMCtx Q} -> {νs} {a : ℒHMType} -> a ≤ b







