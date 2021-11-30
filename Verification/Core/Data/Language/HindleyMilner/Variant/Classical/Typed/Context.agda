
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
-- open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition

open import Verification.Core.Order.Preorder



record _<Γ_ {k} {Q : ℒHMQuant k} {μs νs} (Γ : ℒHMCtxFor Q μs) (Γ' : ℒHMCtxFor Q νs) : 𝒰₀ where
  field fst : μs ⟶ νs
  field snd : Γ ⇃[ fst ]⇂-CtxFor ≡ Γ'
open _<Γ_ public

record SomeℒHMCtxᵘ {k} (Q : ℒHMQuant k) : 𝒰₀ where
  constructor somectx
  field {fst} : ℒHMTypes
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
  _≤-SomeℒHMCtx_ (somectx Γ) (somectx Δ) = Γ <Γ Δ

  reflexive-SomeℒHMCtx : ∀{a} -> a ≤-SomeℒHMCtx a
  reflexive-SomeℒHMCtx = record
    { fst = id
    ; snd = functoriality-id-⇃[]⇂-CtxFor
    }

  _⟡-SomeℒHMCtx_ : ∀{a b c} -> a ≤-SomeℒHMCtx b -> b ≤-SomeℒHMCtx c -> a ≤-SomeℒHMCtx c
  _⟡-SomeℒHMCtx_ {a = somectx Γ₀} {somectx Γ₁} {somectx Γ₂} Γ₀<Γ₁ Γ₁<Γ₂ =
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
module _ {k} {Q : ℒHMQuant k} where
  tail-SomeℒHMCtx : ∀{νsas νsbs μs : ℒHMTypes}
                    -> ∀{as : ℒHMCtxFor Q νsas} {a : ℒHMType ⟨ νsas ⊔ μs ⟩}
                    -> ∀{bs : ℒHMCtxFor Q νsbs} {b : ℒHMType ⟨ νsbs ⊔ μs ⟩}
                    -> somectx {tt ∷ k} (a ∷ as) ≤ somectx (b ∷ bs)
                    -> (somectx as) ≤ (somectx bs)
  tail-SomeℒHMCtx record { fst = fst ; snd = snd } = record { fst = fst ; snd = {!!} }



data ℒHMQuantMap (μs : ℒHMTypes) : ∀{k} (Q R : ℒHMQuant k) -> 𝒰₀ where
  [] : ℒHMQuantMap μs [] []
  _∷_ : ∀{k νs₀ νs₁ Q R} -> (σ : νs₀ ⟶ μs ⊔ νs₁) -> ℒHMQuantMap μs {k} Q R
      -> ℒHMQuantMap μs {tt ∷ k} (νs₀ ∷ Q) (νs₁ ∷ R)

module _ {μs} where
  lookup-ℒHMQuantMap : ∀{k i} -> {Q R : ℒHMQuant k} -> (σ : ℒHMQuantMap μs Q R) -> (k∍i : k ∍♮ i)
                       -> lookup-DList Q k∍i ⟶ μs ⊔ lookup-DList R k∍i
  lookup-ℒHMQuantMap (σ ∷ σs) incl = σ
  lookup-ℒHMQuantMap (σ ∷ σs) (skip k∍i) = lookup-ℒHMQuantMap σs k∍i

  apply-ℒHMQuantMap : ∀{k} {Q R : ℒHMQuant k} -> (ℒHMQuantMap μs Q R) -> ℒHMCtxFor Q μs -> ℒHMCtxFor R μs
  apply-ℒHMQuantMap [] [] = []
  apply-ℒHMQuantMap (σ ∷ σs) (τ ∷ Γ) = τ ⇃[ ⦗ ι₀ , σ ⦘ ]⇂ ∷ apply-ℒHMQuantMap σs Γ


module _ {μs₀} {μs₁} where
  extend-ℒHMQuantMap : ∀{k} {Q R : ℒHMQuant k} -> (μs₀ ⟶ μs₁) -> (ℒHMQuantMap μs₀ Q R) -> (ℒHMQuantMap μs₁ Q R)
  extend-ℒHMQuantMap ϕ [] = []
  extend-ℒHMQuantMap ϕ (σ ∷ σs) = (σ ◆ ϕ ⇃⊔⇂ id) ∷ (extend-ℒHMQuantMap ϕ σs)


module §-ℒHMQuantMap where
  module _ {μs₀} {μs₁} where
    prop-1 : ∀{k} {Q R : ℒHMQuant k} -> (ϕ : μs₀ ⟶ μs₁) -> (σs : ℒHMQuantMap μs₀ Q R)
             -> (Γ : ℒHMCtxFor Q μs₀)
             -> apply-ℒHMQuantMap (extend-ℒHMQuantMap ϕ σs) (Γ ⇃[ ϕ ]⇂ᶜ)
               ≡ (apply-ℒHMQuantMap σs Γ ⇃[ ϕ ]⇂ᶜ)
    prop-1 ϕ [] [] = refl-≡
    prop-1 ϕ (σ ∷ σs) (c ∷ Γ) = λ i -> lem-1 i ∷ prop-1 ϕ σs Γ i
      where
        lem-1 : c ⇃[ ϕ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σ ◆ (ϕ ⇃⊔⇂ id) ⦘ ]⇂ ≡ c ⇃[ ⦗ ι₀ , σ ⦘ ]⇂ ⇃[ ϕ ⇃⊔⇂ id ]⇂
        lem-1 = {!!}

  prop-2 : ∀{k i μs₀} {Q R : ℒHMQuant k} -> (σs : ℒHMQuantMap μs₀ Q R)
            -> (Γ : ℒHMCtxFor Q μs₀)
            -> (k∍i : k ∍♮ i)
            -> lookup-DDList Γ k∍i ⇃[ ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ]⇂
              ≡ lookup-DDList (apply-ℒHMQuantMap σs Γ) k∍i
  prop-2 (σ ∷ σs) (c ∷ Γ) incl = refl-≡
  prop-2 (σ ∷ σs) (c ∷ Γ) (skip k∍i) = prop-2 σs Γ k∍i




sz : ∀{a b : ℒHMTypes} -> a ⟶ b
sz = ⧜subst (construct-D人List λ {tt x → con ℕᵗ ◌-⧜})

ϖ₀ : ∀{a b : ℒHMTypes} -> a ⊔ b ⟶ a
ϖ₀ = ⦗ id , sz ⦘

ϖ₁ : ∀{a b : ℒHMTypes} -> a ⊔ b ⟶ b
ϖ₁ = ⦗ sz , id ⦘

module §-ϖ where
  prop-1 : ∀{a : ℒHMTypes} {f : ⊥ ⟶ a} -> ⦗ id , f ⦘ ◆ ι₀ ∼ id {a = a ⊔ ⊥}
  prop-1 {a} {f} = ⦗ id , f ⦘ ◆ ι₀                  ⟨ append-⦗⦘ ⟩-∼
           ⦗ id ◆ ι₀ , f ◆ ι₀ ⦘                     ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (unit-l-◆ , expand-⊥) ⟩-∼
           ⦗ ι₀ {a = a} {b = ⊥} , elim-⊥ ⦘          ⟨ cong-∼ {{isSetoidHom:⦗⦘}} ((unit-r-◆ ⁻¹) , (expand-⊥ ⁻¹)) ⟩-∼
           ⦗ ι₀ {b = ⊥} ◆ id , ι₁ {a = a} ◆ id ⦘    ⟨ expand-ι₀,ι₁ ⁻¹ ⟩-∼
           id {a = a ⊔ ⊥}                       ∎


  prop-2 : ∀{a b : ℒHMTypes} {f g : (a ⊔ ⊥) ⟶ b} -> ι₀ ◆ f ∼ ι₀ ◆ g -> f ∼ g
  prop-2 = ?

