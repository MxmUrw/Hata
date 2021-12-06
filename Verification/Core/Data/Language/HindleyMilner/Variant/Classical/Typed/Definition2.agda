
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2 where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition

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
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition

open import Verification.Core.Order.Preorder

{-
open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Data.
-- open import Verification.Core.Algebra.Monoid.Free
-- open import Verification.Core.Data.AllOf.Collection.Basics
-- open import Verification.Core.Data.AllOf.Collection.TermTools
-- open import Verification.Core.Category.Std.AllOf.Collection.Basics
-- open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.Category.Subcategory.Full

-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition

-- open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition

open import Verification.Core.Order.Preorder
-}

-- module §-⊔ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
  -- prop-1 : ∀{a b : ⟨ 𝒞 ⟩} -> id {a = a ⊔ b} ∼ ⦗ ι₀ , ι₁ ⦘
  -- prop-1 = {!!}

module §-ℒHMTypes where
  prop-1 : ∀{a b : ℒHMTypes} -> id {a = a ⊔ b} ∼ ⦗ ι₀ , ι₁ ⦘
  prop-1 = {!!}


module §2-isTypedℒHM where

  prop-1 : ∀{k μs te} {Q R : ℒHMQuant k} {Γ : ℒHMCtxFor Q μs} {τ : ℒHMType ⟨ μs ⟩}
        -> (σs : ℒHMQuantMap μs Q R)
        -> isTypedℒHM (μs ⊩ (R , apply-ℒHMQuantMap σs Γ) ⊢ τ) te
        -> isTypedℒHM (μs ⊩ (Q , Γ) ⊢ τ) te
  prop-1 {μs = μs} {Q = Q} {R} {Γ} σs (var k∍i ψ {α} p) = var k∍i ϕ lem-5
    where
      ϕ : lookup-Listᴰ Q k∍i ⟶ μs
      ϕ = lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘

      lem-3 : ⦗ id , lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘ ⦘ ∼ ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ◆ ⦗ id , ψ ⦘
      lem-3 = {!!}
              -- ⦗ id , lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘ ⦘                  ⟨ cong-∼ {{isSetoidHom:⦗⦘}} ((reduce-ι₀ ⁻¹) , refl) ⟩-∼
              -- ⦗ ι₀ ◆ ⦗ id , ψ ⦘ , lookup-ℒHMQuantMap σs k∍i ◆ ⦗ id , ψ ⦘ ⦘     ⟨ append-⦗⦘ ⁻¹ ⟩-∼
              -- ⦗ ι₀ , lookup-ℒHMQuantMap σs k∍i ⦘ ◆ ⦗ id , ψ ⦘    ∎

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
      lem-1 = Γ₁                                    ⟨ inverseCtxProof isAb ⟩-≡
              apply-ℒHMQuantMap σs Γ ⇃[ ϕ ]⇂ᶜ       ⟨ sym-Path (§-ℒHMQuantMap.prop-1 ϕ σs Γ) ⟩-≡
              apply-ℒHMQuantMap σs' (Γ ⇃[ ϕ ]⇂ᶜ)    ∎-≡

      lem-2 : isTypedℒHM (μs₁ ⊩ R , apply-ℒHMQuantMap σs' (Γ ⇃[ ϕ ]⇂ᶜ) ⊢ α) _
      lem-2 = p
              ⟪ transp-isTypedℒHM lem-1 refl-≡ ⟫

      lem-4 : α' ≡ α' ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂
      lem-4 = α'                   ⟨ sym-Path functoriality-id-⇃[]⇂ ⟩-≡
              α' ⇃[ id ]⇂          ⟨ α' ⇃[≀ §-ℒHMTypes.prop-1 ≀]⇂ ⟩-≡
              α' ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂  ∎-≡

      lem-5 : isTypedℒHM (μs ⊩ (κs ∷ R) , ((α' ⇃[ ⦗ ι₀ , ι₁ ⦘ ]⇂) ∷ apply-ℒHMQuantMap σs Γ) ⊢ τ) _
      lem-5 = q
              ⟪ transp-isTypedℒHM ((λ i -> lem-4 i ∷ apply-ℒHMQuantMap σs Γ)) refl-≡ ⟫

      lem-10 : Γ ⇃[ ϕ ]⇂ᶜ ⇃[ ⟨ σ ⟩ ]⇂ᶜ ≡ Γ ⇃[ ι₀ ]⇂ᶜ
      lem-10 = {!!}


