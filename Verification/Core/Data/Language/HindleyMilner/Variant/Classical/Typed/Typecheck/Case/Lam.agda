
{-# OPTIONS --experimental-lossy-unification #-}

module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.Lam where

open import Verification.Conventions hiding (ℕ ; _⊔_) renaming (Σ to PreludeΣ)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2


module _ {𝒯 : 𝒰 𝑖} {{_ : isℒHMTypeCtx {𝑗} 𝒯}} where

  private
    Σ : ℒHMSignature _
    Σ = ′ 𝒯 ′



  -- [Lemma]
  -- | "Inversion of Lam"

  inv-lam : ∀{k μs} {Q : ℒHMQuant Σ k} {Γ : ℒHMCtx Q μs} {τ : ℒHMType Σ μs}
            --------------------------------------
            -- constructor inputs
            -> {te : UntypedℒHM (tt ∷ k)}
            --------------------------------------
            -- condition: is typed
            -> isTypedℒHM (μs ⊩ Γ ⊢ τ) (lam te)
            --------------------------------------
            -- result: we have a lot
            -> ∑ λ (α : ℒHMType Σ (μs ⊔ ⊥))
            -> ∑ λ (β : ℒHMType Σ μs)
            -> (α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β ≡ τ)
                ×-𝒰 isTypedℒHM (μs ⊩ α ∷ Γ ⊢ β) te
  inv-lam (lam te) = _ , _ , refl-≡ , te

  -- //


  -- [Proposition]
  -- | Assuming the induction hypothesis, the /lam/ case is
  --   typecheckable with an initial typing instance.

  -- //


  -- [Proof]
  -- | Let [..], [..], [..], [..] be the input of the
  --   algorithm.
  module typecheck-lam {μs : ℒHMTypes Σ} {k : ♮ℕ} {Q : ℒHMQuant Σ k} (Γ : ℒHMCtx Q μs) where

    -- | Furthermore, assume we have the term [..].
    module _ (te : UntypedℒHM (tt ∷ k)) where

      -- | First we create a context with a new metavariable.

      μs₀ = μs ⊔ st

      αᵘ : ℒHMType Σ st
      αᵘ = varincl

      α₀ : ℒHMType Σ (μs₀ ⊔ ⊥)
      α₀ = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂

      -- create the context which contains this new variable
      Γ₀ : ℒHMCtx Q μs₀
      Γ₀ = Γ ⇃[ ι₀ ]⇂ᶜ

      σ₀ : μs ⟶ μs ⊔ st
      σ₀ = ι₀

      Γ<Γ₀ : Γ <Γ Γ₀
      Γ<Γ₀ = record { fst = ι₀ ; snd = refl-≡ }

      -- | Next, the algorithm computes the typing for |te|,
      --   thus we assume that there is such a typing instance.
      module Success-te (𝑇-te! : PrincipalTypeAssignment (α₀ ∷ Γ₀) te) where

        open PreludeΣ 𝑇-te! renaming
          ( fst to 𝑇-te
          ; snd to Ω
          )

        open TypeAssignment 𝑇-te renaming
          ( metas to μs₁ₐ
          ; typeMetas to μs₁ₓ
          ; ctx to Δ
          ; typ to β₁
          ; isInstance to Δ<α₁Γ₁
          ; hasType to Δ⊢β₁
          )
        -- (μs₁ₐ / μs₁ₓ ⊩ (α₁ ∷ Γ₁) , β₁ , α₀Γ₀<α₁Γ₁ , α₁Γ₁⊢β₁)

        -----------------------------------------
        -- Restoration of |α₁Γ₁ ≡ Δ|

        -- | Now, we restore |α₁Γ₁ ≡ Δ|.
        α₁ = split-Listᴰ² Δ .fst
        Γ₁ = split-Listᴰ² Δ .snd

        -- | Call this one
        α₁Γ₁ : ℒHMCtx (⊥ ∷' Q) μs₁ₐ
        α₁Γ₁ = α₁ ∷ Γ₁

        -- | And we have actually [..] [] [].
        lem-00 : Δ ≡ α₁Γ₁
        lem-00 = §-split-Listᴰ².prop-1

        α₁Γ₁⊢β₁ : isTypedℒHM ((μs₁ₐ ⊔ μs₁ₓ) ⊩ α₁Γ₁ ⇃[ ι₀ ]⇂ᶜ ⊢ β₁) te
        α₁Γ₁⊢β₁ = Δ⊢β₁
                    ⟪ transp-isTypedℒHM (cong (_⇃[ ι₀ ]⇂ᶜ) lem-00) refl-≡ ⟫

        -----------------------------------------
        -- actual proof

        -- | The following definitions follow.
        σᵃ₀₁ : μs₀ ⟶ μs₁ₐ
        σᵃ₀₁ = Δ<α₁Γ₁ .fst

        Γ₀<Γ₁ : Γ₀ <Γ Γ₁
        Γ₀<Γ₁ = record { fst = σᵃ₀₁ ; snd = λ i -> split-Listᴰ² (snd Δ<α₁Γ₁ i) .snd }

        f : μs ⟶ μs₁ₐ
        f = ι₀ ◆ σᵃ₀₁

        factor:f = factorize f

        μs₂ₐ = image factor:f
        μs₂ₓ = rest factor:f
        μs₂ = μs₂ₐ ⊔ μs₂ₓ

        σᵃᵤ₂ : μs ⟶ μs₂ₐ
        σᵃᵤ₂ = epiHom factor:f

        ϕ : μs₂ ≅ μs₁ₐ
        ϕ = splitting factor:f

        lem-0 : ι₀ ◆ σᵃ₀₁ ◆ ⟨ ϕ ⟩⁻¹ ∼ σᵃᵤ₂ ◆ ι₀
        lem-0 = factors factor:f

        Γ₂ = Γ ⇃[ σᵃᵤ₂ ]⇂ᶜ

        あ : (μs₂ₐ ⊔ μs₂ₓ) ⊔ μs₁ₓ ≅ μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ)
        あ = assoc-l-⊔-ℒHMTypes

        ψ⁻¹ : (μs₁ₐ ⊔ μs₁ₓ) ⟶ μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ)
        ψ⁻¹ = (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩

        α₂ : ℒHMType Σ (μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ))
        α₂ = α₁ ⇃[ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ]⇂


        β₂ : ℒHMType Σ (μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ))
        β₂ = β₁ ⇃[ ψ⁻¹ ]⇂

        module lem-03 where abstract
          Proof : ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ ψ⁻¹)) ∼ σᵃᵤ₂ ◆ ι₀
          Proof = ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ ((⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩)))

                    ⟨ refl ◈ (refl ◈ assoc-r-◆ ) ⟩-∼

                    ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩))

                    ⟨ refl ◈ (refl ◈ (reduce-ι₀ ◈ refl) ) ⟩-∼

                    ι₀ ◆ (σᵃ₀₁ ◆ (⟨ ϕ ⟩⁻¹ ◆ ι₀ ◆ ⟨ あ ⟩))

                    ⟨ refl ◈ (refl ◈ (assoc-l-◆) ) ⟩-∼

                    ι₀ ◆ (σᵃ₀₁ ◆ (⟨ ϕ ⟩⁻¹ ◆ (ι₀ ◆ ⟨ あ ⟩)))

                    ⟨ refl ◈ (assoc-r-◆) ⟩-∼

                    ι₀ ◆ ((σᵃ₀₁ ◆ ⟨ ϕ ⟩⁻¹) ◆ (ι₀ ◆ ⟨ あ ⟩))

                    ⟨ (assoc-r-◆) ⟩-∼

                    (ι₀ ◆ (σᵃ₀₁ ◆ ⟨ ϕ ⟩⁻¹)) ◆ (ι₀ ◆ ⟨ あ ⟩)

                    ⟨ (assoc-r-◆) ◈ refl ⟩-∼

                    ((ι₀ ◆ σᵃ₀₁) ◆ ⟨ ϕ ⟩⁻¹) ◆ (ι₀ ◆ ⟨ あ ⟩)

                    ⟨ lem-0 ◈ refl ⟩-∼

                    (σᵃᵤ₂ ◆ ι₀) ◆ (ι₀ ◆ ⟨ あ ⟩)

                    ⟨ assoc-l-◆ ⟩-∼

                    σᵃᵤ₂ ◆ (ι₀ ◆ (ι₀ ◆ ⟨ あ ⟩))

                    ⟨ refl ◈ assoc-r-◆ ⟩-∼

                    σᵃᵤ₂ ◆ ((ι₀ ◆ ι₀) ◆ ⟨ あ ⟩)

                    ⟨ refl ◈ §-assoc-l-⊔-ℒHMTypes.prop-1 ⟩-∼

                    σᵃᵤ₂ ◆ ι₀

                    ∎



        module lem-04a where abstract
          Proof : Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ψ⁻¹ ]⇂ᶜ ≡ Γ ⇃[ σᵃᵤ₂ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
          Proof =   Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ψ⁻¹ ]⇂ᶜ      ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₁} {f = ι₀} {ψ⁻¹} ⟩-≡
                    Γ₁ ⇃[ ι₀ ◆ ψ⁻¹ ]⇂ᶜ           ⟨ cong _⇃[ ι₀ ◆ ψ⁻¹ ]⇂ᶜ (sym-Path (snd Γ₀<Γ₁)) ⟩-≡
                    Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ◆ ψ⁻¹ ]⇂ᶜ   ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ ⇃[ ι₀ ]⇂ᶜ} ⟩-≡
                    Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₁ ◆ (ι₀ ◆ ψ⁻¹) ]⇂ᶜ   ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                    Γ ⇃[ ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ ψ⁻¹)) ]⇂ᶜ       ⟨ Γ ⇃[≀ lem-03.Proof ≀]⇂ᶜ ⟩-≡
                    Γ ⇃[ σᵃᵤ₂ ◆ ι₀ ]⇂ᶜ           ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ}) ⟩-≡
                    Γ ⇃[ σᵃᵤ₂ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ      ∎-≡


        module lem-04b where abstract
          Proof : α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ψ⁻¹ ]⇂ ≡ α₂
          Proof = α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ψ⁻¹ ]⇂

                    ⟨ cong _⇃[ ψ⁻¹ ]⇂ (functoriality-◆-⇃[]⇂ {τ = α₁} {f = (ι₀ ⇃⊔⇂ id)} {⦗ id , elim-⊥ ⦘}) ⟩-≡

                    α₁ ⇃[ (ι₀ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ψ⁻¹ ]⇂

                    ⟨ functoriality-◆-⇃[]⇂ {τ = α₁} {f = (ι₀ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘} {g = ψ⁻¹} ⟩-≡

                    α₁ ⇃[ (ι₀ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ◆ ψ⁻¹ ]⇂

                    ⟨ α₁ ⇃[≀ lem-04bi ≀]⇂ ⟩-≡

                    α₂

                    ∎-≡

            where
              lem-04bi : (ι₀ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ◆ ψ⁻¹ ∼ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘
              lem-04bi = (ι₀ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ◆ ψ⁻¹  ⟨ append-⇃⊔⇂ ◈ refl ⟩-∼
                          ⦗ (ι₀ ◆ id , id ◆ elim-⊥) ⦘ ◆ ψ⁻¹    ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (unit-r-◆ , unit-l-◆)◈ refl ⟩-∼
                          ⦗ (ι₀ , elim-⊥) ⦘ ◆ ψ⁻¹              ⟨ append-⦗⦘ ⟩-∼
                          ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ◆ ψ⁻¹ ⦘          ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (refl , expand-⊥) ⟩-∼
                          ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘                ∎


        module lem-05 where abstract
          Proof : isTypedℒHM (μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ) ⊩ (Γ₂ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₂ ⇒ β₂) (lam te)
          Proof = lam α₁Γ₁⊢β₁
                  ⟪ §-isTypedℒHM.prop-2 ψ⁻¹ ⟫
                  ⟪ transp-isTypedℒHM refl-≡ §-⇃[]⇂.prop-1 ⟫
                  >> isTypedℒHM ((μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ)) ⊩ Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ψ⁻¹ ]⇂ᶜ ⊢ _ ⇒ β₂) (lam te) <<

                  ⟪ transp-isTypedℒHM lem-04a.Proof (λ i -> lem-04b.Proof i ⇒ β₂) ⟫

        Γ<Γ₂ : Γ <Γ Γ₂
        Γ<Γ₂ = record { fst = σᵃᵤ₂ ; snd = refl-≡ }

        -- | Finally we get a typing instance [..] given by [....]

        𝑇 : TypeAssignment Γ (lam te)
        𝑇 = μs₂ₐ / (μs₂ₓ ⊔ μs₁ₓ) ⊩ Γ₂ , α₂ ⇒ β₂ , Γ<Γ₂ , (lem-05.Proof)

        -- | Now we want to show that this is the initial typing instance.
        -- | > Assume we are given another typing instance.
        module _ (𝑆 : TypeAssignment Γ (lam te)) where
          open TypeAssignment 𝑆 renaming
            ( metas to μs₃ₐ
            ; typeMetas to μs₃ₓ
            ; ctx to Γ₃
            ; typ to δ₃
            ; isInstance to Γ<Γ₃
            ; hasType to Γ₃⊢δ₃
            )

          -- | We know that the lam typing must have been derived by the
          --   lam rule.
          inR = inv-lam Γ₃⊢δ₃
          α₃ = inR .fst
          β₃ = inR .snd .fst
          α₃⇒β₃=δ₃ = inR .snd .snd .fst
          Γ₃α₃⊢β₃ = inR .snd .snd .snd


          -- | The actual proof.
          σᵃᵤ₃ : μs ⟶ μs₃ₐ
          σᵃᵤ₃ = Γ<Γ₃ .fst

          β₃' : ℒHMType Σ (μs₃ₐ ⊔ μs₃ₓ ⊔ ⊥)
          β₃' = β₃ ⇃[ ι₀ ]⇂

          Γ₃' : ℒHMCtx _ (μs₃ₐ ⊔ μs₃ₓ)
          Γ₃' = Γ₃ ⇃[ ι₀ ]⇂ᶜ

          lem-9 : isTypedℒHM (μs₃ₐ ⊔ μs₃ₓ ⊔ ⊥ ⊩ (α₃ ∷ Γ₃') ⇃[ ι₀ ]⇂ᶜ ⊢ β₃') te
          lem-9 = Γ₃α₃⊢β₃
                  ⟪ §-isTypedℒHM.prop-2 ι₀ ⟫

          α₃' : ℒHMType Σ (μs₃ₐ ⊔ μs₃ₓ)
          α₃' = α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

          σα₃ : st ⟶ μs₃ₐ ⊔ μs₃ₓ
          σα₃ = α₃' -- ⧜subst (incl α₃')

          σᵃ₀₃ : μs₀ ⟶ μs₃ₐ ⊔ μs₃ₓ
          σᵃ₀₃ = ⦗ σᵃᵤ₃ ◆ ι₀ , σα₃ ⦘

          -- | Now some lemma.
          module lem-10a where abstract
            private
              P-0 : ι₁ ◆ ι₀ {b = ⊥} ◆ (σᵃ₀₃ ⇃⊔⇂ id) ∼ σα₃ ◆ ι₀
              P-0 = ι₁ ◆ ι₀ {b = ⊥} ◆ (σᵃ₀₃ ⇃⊔⇂ id)     ⟨ assoc-l-◆ ⟩-∼
                          ι₁ ◆ (ι₀ ◆ (σᵃ₀₃ ⇃⊔⇂ id))   ⟨ refl ◈ reduce-ι₀ ⟩-∼
                          ι₁ ◆ (σᵃ₀₃ ◆ ι₀)            ⟨ assoc-r-◆ ⟩-∼
                          (ι₁ ◆ σᵃ₀₃) ◆ ι₀            ⟨ reduce-ι₁ ◈ refl ⟩-∼
                          (σα₃) ◆ ι₀                   ∎

            Proof  : α₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂ ≡ α₃
            Proof = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂     ⟨ functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = ι₁ ◆ ι₀} {σᵃ₀₃ ⇃⊔⇂ id} ⟩-≡
                    αᵘ ⇃[ ι₁ ◆ ι₀ ◆ (σᵃ₀₃ ⇃⊔⇂ id) ]⇂       ⟨ αᵘ ⇃[≀ P-0 ≀]⇂ ⟩-≡
                    αᵘ ⇃[ σα₃ ◆ ι₀ ]⇂                       ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = σα₃} {ι₀}) ⟩-≡
                    -- here we need to use the fact that ⇃[ σα₃ ]⇂, applied to `incl`
                    -- gives us the value of that incl. (since the substitution is abstract)
                    αᵘ ⇃[ σα₃ ]⇂ ⇃[ ι₀ ]⇂                   ⟨ cong _⇃[ ι₀ ]⇂ (§-⇃[]⇂.prop-2) ⟩-≡
                    α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ι₀ ]⇂       ⟨ functoriality-◆-⇃[]⇂ {τ = α₃} {f = ⦗ id , elim-⊥ ⦘} {ι₀} ⟩-≡
                    α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ◆ ι₀ ]⇂           ⟨ α₃ ⇃[≀ §-ϖ.prop-1  ≀]⇂ ⟩-≡
                    α₃ ⇃[ id ]⇂                             ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                    α₃                                      ∎-≡

          -- | And lemma 10b!?
          module lem-10b where abstract
            Proof : Γ₀ ⇃[ σᵃ₀₃ ]⇂ᶜ ≡ Γ₃'
            Proof = Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₃ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                    Γ ⇃[ ι₀ ◆ σᵃ₀₃ ]⇂ᶜ       ⟨ Γ ⇃[≀ reduce-ι₀ ≀]⇂ᶜ ⟩-≡
                    Γ ⇃[ σᵃᵤ₃ ◆ ι₀ ]⇂ᶜ        ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ}) ⟩-≡
                    Γ ⇃[ σᵃᵤ₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ   ⟨ cong _⇃[ ι₀ ]⇂ᶜ (snd Γ<Γ₃) ⟩-≡
                    Γ₃ ⇃[ ι₀ ]⇂ᶜ              ∎-≡

          α₀Γ₀<α₃Γ₃' : (α₀ ∷' Γ₀) <Γ (α₃ ∷ Γ₃')
          α₀Γ₀<α₃Γ₃' = record { fst = σᵃ₀₃ ; snd = λ i → lem-10a.Proof i ∷ lem-10b.Proof i }


          𝑆-te : TypeAssignment (α₀ ∷' Γ₀) te
          𝑆-te = ((μs₃ₐ ⊔ μs₃ₓ) / ⊥ ⊩ α₃ ∷ Γ₃' , β₃' , α₀Γ₀<α₃Γ₃' , lem-9)

          module ΩR where abstract
            Proof : 𝑇-te <TI 𝑆-te
            Proof = Ω ((μs₃ₐ ⊔ μs₃ₓ) / ⊥ ⊩ α₃ ∷ Γ₃' , β₃' , α₀Γ₀<α₃Γ₃' , lem-9)

          σᵃ₁₃ : μs₁ₐ ⟶ μs₃ₐ ⊔ μs₃ₓ
          σᵃ₁₃ = tiSubₐ ΩR.Proof

          σˣ₁₃ : μs₁ₓ ⟶ (μs₃ₐ ⊔ μs₃ₓ) ⊔ ⊥
          σˣ₁₃ = tiSubₓ ΩR.Proof

          σᵃ₂₃ : μs₂ₐ ⟶ μs₃ₐ
          σᵃ₂₃ = ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ ◆ ϖ₀
          -- σ₂₃ ◆ ϖ₀

          σˣ₂₃ : (μs₂ₓ ⊔ μs₁ₓ) ⟶ μs₃ₐ ⊔ μs₃ₓ
          σˣ₂₃ = ⦗ ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘


          -- | And look at nr 15, how great!
          module lem-15 where abstract
            Proof : σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩) ∼ ι₀ ◆ σᵃ₀₁
            Proof = σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩)             ⟨ assoc-r-◆ ⟩-∼
                    (σᵃᵤ₂ ◆ ι₀) ◆ ⟨ ϕ ⟩             ⟨ lem-0 ⁻¹ ◈ refl ⟩-∼
                    ι₀ ◆ σᵃ₀₁ ◆ ⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩     ⟨ assoc-l-◆ ⟩-∼
                    ι₀ ◆ σᵃ₀₁ ◆ (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩)   ⟨ refl ◈ inv-l-◆ (of ϕ) ⟩-∼
                    ι₀ ◆ σᵃ₀₁ ◆ id                 ⟨ unit-r-◆ ⟩-∼
                    ι₀ ◆ σᵃ₀₁                      ∎

          module lem-16 where abstract
            Proof : σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃) ∼ σᵃᵤ₃ ◆ ι₀
            Proof = σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃)     ⟨ assoc-r-◆ ⟩-∼
                    σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩) ◆ σᵃ₁₃     ⟨ lem-15.Proof ◈ refl ⟩-∼
                    ι₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃               ⟨ assoc-l-◆ ⟩-∼
                    ι₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₃)             ⟨ refl ◈ subProof ΩR.Proof ⟩-∼
                    ι₀ ◆ (σᵃ₀₃)                   ⟨ reduce-ι₀ ⟩-∼
                    (σᵃᵤ₃ ◆ ι₀)                    ∎

          module lem-20 where abstract
            Proof : σᵃᵤ₂ ◆ σᵃ₂₃ ∼ σᵃᵤ₃
            Proof = σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ ◆ ϖ₀)  ⟨ assoc-r-◆ ⟩-∼
                    σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃) ◆ ϖ₀  ⟨ lem-16.Proof ◈ refl ⟩-∼
                    σᵃᵤ₃ ◆ ι₀ ◆ ϖ₀                   ⟨ assoc-l-◆ ⟩-∼
                    σᵃᵤ₃ ◆ (ι₀ ◆ ϖ₀)                 ⟨ refl ◈ reduce-ι₀ ⟩-∼
                    σᵃᵤ₃ ◆ id                        ⟨ unit-r-◆ ⟩-∼
                    σᵃᵤ₃                             ∎

          -- | Also here, super, right?
          module lem-30 where abstract
            Proof : σᵃ₂₃ ◆ ι₀ ∼ ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃
            Proof = cancel-epi {{_}} {{isEpi:epiHom factor:f}} lem-30a
              where
                lem-30a : σᵃᵤ₂ ◆ (σᵃ₂₃ ◆ ι₀) ∼ σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃)
                lem-30a = σᵃᵤ₂ ◆ (σᵃ₂₃ ◆ ι₀)           ⟨ assoc-r-◆ ⟩-∼
                          (σᵃᵤ₂ ◆ σᵃ₂₃) ◆ ι₀           ⟨ lem-20.Proof ◈ refl ⟩-∼
                          σᵃᵤ₃ ◆ ι₀                    ⟨ lem-16.Proof ⁻¹ ⟩-∼
                          σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃)   ∎


          -------------------------------------------------
          -- these lemmas are needed for the α₂ ⇃[ "σ₂₃" ]⇂ ≡ α₃ proof
          module lem-31 where abstract
            Proof : ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ∼ ⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘
            Proof = ⦗ σᵃ₂₃ ◆ ι₀ , ⦗ ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘ ⦘

                    ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (lem-30.Proof , refl) ⟩-∼

                    ⦗ ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , ⦗ ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘ ⦘

                    ⟨ §-assoc-l-⊔-ℒHMTypes.prop-2 ⟩-∼

                    ⟨ あ ⟩⁻¹ ◆ ⦗ ⦗ ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ ⦘ , σˣ₁₃ ◆ ϖ₀ ⦘

                    ⟨ refl ◈ ⦗≀ ⦗≀ assoc-l-◆ , assoc-l-◆ ≀⦘ , refl ≀⦘ ⟩-∼

                    ⟨ あ ⟩⁻¹ ◆ ⦗ ⦗ ι₀ ◆ (⟨ ϕ ⟩ ◆ σᵃ₁₃) , ι₁ ◆ (⟨ ϕ ⟩ ◆ σᵃ₁₃) ⦘ , σˣ₁₃ ◆ ϖ₀ ⦘

                    ⟨ refl ◈ ⦗≀ expand-ι₀,ι₁ ⁻¹ , refl ≀⦘ ⟩-∼

                    ⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘

                    ∎

          -- | And nr 32, that is almost 42.
          module lem-32 where abstract
            Proof : ψ⁻¹ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘) ∼ ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘
            Proof = (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩ ◆ (⟨ あ ⟩⁻¹ ◆ _)

                    ⟨ assoc-r-◆ ⟩-∼

                    (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩ ◆ ⟨ あ ⟩⁻¹ ◆ _

                    ⟨ assoc-l-◆ ◈ refl ⟩-∼

                    (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ (⟨ あ ⟩ ◆ ⟨ あ ⟩⁻¹) ◆ _

                    ⟨ refl ◈ (inv-r-◆ (of あ)) ◈ refl ⟩-∼

                    (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ id ◆ _

                    ⟨ unit-r-◆ ◈ refl ⟩-∼

                    (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘

                    ⟨ append-⇃⊔⇂ ⟩-∼

                    ⦗ ⟨ ϕ ⟩⁻¹ ◆ (⟨ ϕ ⟩ ◆ σᵃ₁₃) , id ◆ (σˣ₁₃ ◆ ϖ₀) ⦘

                    ⟨ ⦗≀ assoc-r-◆ ∙ (inv-l-◆ (of ϕ) ◈ refl) ∙ unit-l-◆ , unit-l-◆ ≀⦘ ⟩-∼

                    ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘

                    ∎

          module lem-33 where abstract
            Proof : ι₀ ◆ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘) ∼ σᵃ₁₃
            Proof = ι₀ ◆ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ _

                    ⟨ reduce-ι₀ ◈ refl ⟩-∼

                    ι₀ ◆ ψ⁻¹ ◆ _

                    ⟨ assoc-l-◆ ⟩-∼

                    ι₀ ◆ (ψ⁻¹ ◆ _)

                    ⟨ refl ◈ lem-32.Proof ⟩-∼

                    ι₀ ◆ ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘

                    ⟨ reduce-ι₀ ⟩-∼

                    σᵃ₁₃

                    ∎

          module lem-34 where abstract
            Proof : ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘) ∼ (σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘
            Proof = §-ϖ.prop-2 lem-34a
              where
                lem-34a : ι₀ ◆ (⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘)) ∼ ι₀ ◆ ((σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘)
                lem-34a = ι₀ ◆ (⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘))

                          ⟨ refl ◈ (refl ◈ lem-31.Proof ) ⟩-∼

                          ι₀ ◆ (⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘))

                          ⟨ assoc-r-◆ ⟩-∼

                          (ι₀ ◆ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘) ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘)

                          ⟨ lem-33.Proof ⟩-∼

                          σᵃ₁₃

                          ⟨ unit-r-◆ ⁻¹ ⟩-∼

                          σᵃ₁₃ ◆ id

                          ⟨ refl ◈ reduce-ι₀ ⁻¹ ⟩-∼

                          σᵃ₁₃ ◆ (ι₀  ◆ ⦗ id , elim-⊥ ⦘)

                          ⟨ assoc-r-◆ ⟩-∼

                          (σᵃ₁₃ ◆ ι₀ ) ◆ ⦗ id , elim-⊥ ⦘

                          ⟨ reduce-ι₀ ⁻¹ ◈ refl ⟩-∼

                          (ι₀ ◆ (σᵃ₁₃ ⇃⊔⇂ id)) ◆ ⦗ id , elim-⊥ ⦘

                          ⟨ assoc-l-◆ ⟩-∼

                          ι₀ ◆ ((σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘)

                          ∎


          -- | Maybe this one's great as well.
          module lem-35 where abstract
            Proof : α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂ ≡ α₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂
            Proof = α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂                         ⟨ sym-Path (cong _⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂ (λ i -> split-Listᴰ² (Δ<α₁Γ₁ .snd i) .fst)) ⟩-≡
                    α₀ ⇃[ (σᵃ₀₁ ⇃⊔⇂ id) ]⇂ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂     ⟨ functoriality-◆-⇃[]⇂ {τ = α₀} {f = (σᵃ₀₁ ⇃⊔⇂ id)} {(σᵃ₁₃ ⇃⊔⇂ id)} ⟩-≡
                    α₀ ⇃[ (σᵃ₀₁ ⇃⊔⇂ id) ◆ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂         ⟨ α₀ ⇃[≀ functoriality-◆-⊔ ⁻¹ ≀]⇂ ⟩-≡
                    α₀ ⇃[ ((σᵃ₀₁ ◆ σᵃ₁₃) ⇃⊔⇂ (id ◆ id)) ]⇂             ⟨ α₀ ⇃[≀ subProof ΩR.Proof ≀⇃⊔⇂≀ unit-2-◆ ≀]⇂ ⟩-≡
                    α₀ ⇃[ (σᵃ₀₃ ⇃⊔⇂ id) ]⇂                        ∎-≡

          module lem-40 where abstract
            Proof : α₂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂ ≡ α₃'
            Proof = α₁ ⇃[ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂

                    ⟨ functoriality-◆-⇃[]⇂ {τ = α₁} {f = ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘} {⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘} ⟩-≡

                    α₁ ⇃[ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂

                    ⟨ α₁ ⇃[≀ lem-34.Proof ≀]⇂ ⟩-≡

                    α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ]⇂

                    ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α₁} {f = (σᵃ₁₃ ⇃⊔⇂ id)} {⦗ id , elim-⊥ ⦘}) ⟩-≡

                    α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

                    ⟨ cong _⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ lem-35.Proof ⟩-≡

                    α₀ ⇃[ (σᵃ₀₃ ⇃⊔⇂ id) ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

                    ⟨ cong _⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ (λ i -> split-Listᴰ² (α₀Γ₀<α₃Γ₃' .snd i) .fst) ⟩-≡

                    α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

                    ⟨ refl-≡ ⟩-≡

                    α₃'

                    ∎-≡


          -------------------------------------------------------
          -- now the lemmas for β₂ ⇃[ "σ₂₃" ]⇂ ≡ β₃ proof

          -- | Well look here, we are almost done.
          module lem-41 where abstract
            Proof : β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀ ]⇂ ≡ β₃'
            Proof = β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀ ]⇂

                    ⟨ (functoriality-◆-⇃[]⇂ {τ = β₁} {f = ψ⁻¹} {⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀}) ⟩-≡

                    β₁ ⇃[ ψ⁻¹ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ]⇂

                    ⟨ β₁ ⇃[≀ lem-41a ≀]⇂ ⟩-≡

                    β₁ ⇃[ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘ ]⇂

                    ⟨ typProof ΩR.Proof ⟩-≡

                    β₃'

                    ∎-≡

              where
                lem-41a : ψ⁻¹ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ∼ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘
                lem-41a = ψ⁻¹ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀)

                      ⟨ assoc-r-◆ ⟩-∼

                      (ψ⁻¹ ◆ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘) ◆ ι₀

                      ⟨ (refl ◈ lem-31.Proof) ◈ refl ⟩-∼

                      ψ⁻¹ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘) ◆ ι₀

                      ⟨ lem-32.Proof ◈ refl ⟩-∼

                      ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘ ◆ ι₀

                      ⟨ append-⦗⦘ ⟩-∼

                      ⦗ σᵃ₁₃ ◆ ι₀ , (σˣ₁₃ ◆ ϖ₀) ◆ ι₀ ⦘

                      ⟨ ⦗≀ refl , assoc-l-◆ ≀⦘ ⟩-∼

                      ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ◆ (ϖ₀ ◆ ι₀) ⦘

                      ⟨ ⦗≀ refl , ((refl ◈ §-ϖ.prop-1) ∙ unit-r-◆) ≀⦘ ⟩-∼

                      ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘

                      ∎

          -- | And wow, we did reach 42.
          module lem-42 where abstract
            Proof : β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂ ≡ β₃
            Proof = β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂

                    ⟨ β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[≀ unit-r-◆ ⁻¹ ∙ (refl ◈ reduce-ι₀ ⁻¹) ∙ assoc-r-◆ ≀]⇂ ⟩-≡

                    β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ◆ ϖ₀ ]⇂

                    ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = β₁ ⇃[ ψ⁻¹ ]⇂} {f = (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀)} {ϖ₀}) ⟩-≡

                    β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ]⇂ ⇃[ ϖ₀ ]⇂

                    ⟨ cong _⇃[ ϖ₀ ]⇂ lem-41.Proof ⟩-≡

                    β₃ ⇃[ ι₀ ]⇂ ⇃[ ϖ₀ ]⇂

                    ⟨ functoriality-◆-⇃[]⇂ {τ = β₃} {f = ι₀} {ϖ₀} ⟩-≡

                    β₃ ⇃[ ι₀ ◆ ϖ₀ ]⇂

                    ⟨ β₃ ⇃[≀ reduce-ι₀ ≀]⇂ ⟩-≡

                    β₃ ⇃[ id ]⇂

                    ⟨ functoriality-id-⇃[]⇂ ⟩-≡

                    β₃

                    ∎-≡


          -- | Which means that here is our result!
          -- here we additionally need that ⇒ distributes over substitution (or the other way round)
          lem-50 : (α₂ ⇒ β₂) ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂ ≡ α₃' ⇒ β₃
          lem-50 = trans-Path (§-⇃[]⇂.prop-1) (λ i -> lem-40.Proof i ⇒ lem-42.Proof i)

          -- | But what exactly is your problem then ?

          isInitial:𝑇 : 𝑇 <TI 𝑆
          isInitial:𝑇 = record { tiSubₐ = σᵃ₂₃ ; tiSubₓ = σˣ₂₃ ; typProof = trans-Path lem-50 α₃⇒β₃=δ₃ ; subProof = lem-20.Proof }

        Result : PrincipalTypeAssignment Γ (lam te)
        Result = 𝑇 , isInitial:𝑇

      ---------------------------------------------------------------
      -- FAIL (no te typing)
      ---------------------------------------------------------------
      --{}
      -- NOTE:
      -- This is literally the same code as part of the initiality
      -- proof above. With some other architecture / definitions
      -- one should surely be able to prove both at the same time.
      --{}

      -- | Now, for the case where there is no typing for |te|.
      module Fail-te (¬𝑇-te : ¬ TypeAssignment (α₀ ∷ Γ₀) te) where

        -- | Then we also do not have a typing instance.
        --   To show that, assume that we had one.

        --------------------------------------
        -- DUPLICATE CODE BEGIN

        module _ (𝑆 : TypeAssignment Γ (lam te)) where
          open TypeAssignment 𝑆 renaming
            ( metas to μs₃ₐ
            ; typeMetas to μs₃ₓ
            ; ctx to Γ₃
            ; typ to δ₃
            ; isInstance to Γ<Γ₃
            ; hasType to Γ₃⊢δ₃
            )

          -- | We know that the lam typing must have been derived by the
          --   lam rule.
          inR = inv-lam Γ₃⊢δ₃
          α₃ = inR .fst
          β₃ = inR .snd .fst
          α₃⇒β₃=δ₃ = inR .snd .snd .fst
          Γ₃α₃⊢β₃ = inR .snd .snd .snd

          -- | The actual proof.
          σᵃᵤ₃ : μs ⟶ μs₃ₐ
          σᵃᵤ₃ = Γ<Γ₃ .fst

          β₃' : ℒHMType Σ (μs₃ₐ ⊔ μs₃ₓ ⊔ ⊥)
          β₃' = β₃ ⇃[ ι₀ ]⇂

          Γ₃' : ℒHMCtx _ (μs₃ₐ ⊔ μs₃ₓ)
          Γ₃' = Γ₃ ⇃[ ι₀ ]⇂ᶜ

          lem-9 : isTypedℒHM (μs₃ₐ ⊔ μs₃ₓ ⊔ ⊥ ⊩ (α₃ ∷ Γ₃') ⇃[ ι₀ ]⇂ᶜ ⊢ β₃') te
          lem-9 = Γ₃α₃⊢β₃
                  ⟪ §-isTypedℒHM.prop-2 ι₀ ⟫

          α₃' : ℒHMType Σ (μs₃ₐ ⊔ μs₃ₓ)
          α₃' = α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

          σα₃ : st ⟶ μs₃ₐ ⊔ μs₃ₓ
          σα₃ = α₃' --  ⧜subst (incl α₃')

          σᵃ₀₃ : μs₀ ⟶ μs₃ₐ ⊔ μs₃ₓ
          σᵃ₀₃ = ⦗ σᵃᵤ₃ ◆ ι₀ , σα₃ ⦘

          -- | Now some lemma.
          module lem-10a where abstract
            private
              P-0 : ι₁ ◆ ι₀ {b = ⊥} ◆ (σᵃ₀₃ ⇃⊔⇂ id) ∼ σα₃ ◆ ι₀
              P-0 = ι₁ ◆ ι₀ {b = ⊥} ◆ (σᵃ₀₃ ⇃⊔⇂ id)     ⟨ assoc-l-◆ ⟩-∼
                          ι₁ ◆ (ι₀ ◆ (σᵃ₀₃ ⇃⊔⇂ id))   ⟨ refl ◈ reduce-ι₀ ⟩-∼
                          ι₁ ◆ (σᵃ₀₃ ◆ ι₀)            ⟨ assoc-r-◆ ⟩-∼
                          (ι₁ ◆ σᵃ₀₃) ◆ ι₀            ⟨ reduce-ι₁ ◈ refl ⟩-∼
                          (σα₃) ◆ ι₀                   ∎

            Proof  : α₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂ ≡ α₃
            Proof = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂     ⟨ functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = ι₁ ◆ ι₀} {σᵃ₀₃ ⇃⊔⇂ id} ⟩-≡
                    αᵘ ⇃[ ι₁ ◆ ι₀ ◆ (σᵃ₀₃ ⇃⊔⇂ id) ]⇂       ⟨ αᵘ ⇃[≀ P-0 ≀]⇂ ⟩-≡
                    αᵘ ⇃[ σα₃ ◆ ι₀ ]⇂                       ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = σα₃} {ι₀}) ⟩-≡
                    -- here we need to use the fact that ⇃[ σα₃ ]⇂, applied to `incl`
                    -- gives us the value of that incl. (since the substitution is abstract)
                    αᵘ ⇃[ σα₃ ]⇂ ⇃[ ι₀ ]⇂                   ⟨ cong _⇃[ ι₀ ]⇂ (§-⇃[]⇂.prop-2) ⟩-≡
                    α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ι₀ ]⇂       ⟨ functoriality-◆-⇃[]⇂ {τ = α₃} {f = ⦗ id , elim-⊥ ⦘} {ι₀} ⟩-≡
                    α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ◆ ι₀ ]⇂           ⟨ α₃ ⇃[≀ §-ϖ.prop-1  ≀]⇂ ⟩-≡
                    α₃ ⇃[ id ]⇂                             ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                    α₃                                      ∎-≡

          -- | And lemma 10b!?
          module lem-10b where abstract
            Proof : Γ₀ ⇃[ σᵃ₀₃ ]⇂ᶜ ≡ Γ₃'
            Proof = Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₃ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                    Γ ⇃[ ι₀ ◆ σᵃ₀₃ ]⇂ᶜ       ⟨ Γ ⇃[≀ reduce-ι₀ ≀]⇂ᶜ ⟩-≡
                    Γ ⇃[ σᵃᵤ₃ ◆ ι₀ ]⇂ᶜ        ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ}) ⟩-≡
                    Γ ⇃[ σᵃᵤ₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ   ⟨ cong _⇃[ ι₀ ]⇂ᶜ (snd Γ<Γ₃) ⟩-≡
                    Γ₃ ⇃[ ι₀ ]⇂ᶜ              ∎-≡

          α₀Γ₀<α₃Γ₃' : (α₀ ∷' Γ₀) <Γ (α₃ ∷ Γ₃')
          α₀Γ₀<α₃Γ₃' = record { fst = σᵃ₀₃ ; snd = λ i → lem-10a.Proof i ∷ lem-10b.Proof i }


          𝑆-te : TypeAssignment (α₀ ∷' Γ₀) te
          𝑆-te = ((μs₃ₐ ⊔ μs₃ₓ) / ⊥ ⊩ α₃ ∷ Γ₃' , β₃' , α₀Γ₀<α₃Γ₃' , lem-9)

          -- SAME CODE END
          --------------------------------------

          Result : 𝟘-𝒰
          Result = ¬𝑇-te 𝑆-te

  -- //


