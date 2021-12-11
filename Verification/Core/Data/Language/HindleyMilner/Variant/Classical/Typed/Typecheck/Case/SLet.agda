
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.SLet where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports


open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.MetaVarReduction
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2




-- [Lemma]
-- | "Inversion of SLet". The following holds.

inv-slet : ∀{k νs} {Q : ℒHMQuant k} {Γ' : ℒHMCtx Q νs} {β : ℒHMType ⟨ νs ⟩}
           --------------------------------------
           -- constructor inputs
           -> {te₀ : UntypedℒHM k} {te₁ : UntypedℒHM (tt ∷ k)}
           --------------------------------------
           -- condition: is typed
           -> isTypedℒHM (νs ⊩ Γ' ⊢ β) (slet te₀ te₁)
           --------------------------------------
           -- result: we have a lot
           -> ∑ λ μs -> ∑ λ κs -> ∑ λ (Γ : ℒHMCtx Q μs)
           -> ∑ λ (α : ℒHMType ⟨ μs ⟩)
           -> ∑ λ (α' : ℒHMType ⟨ νs ⊔ κs ⟩)
           -> isAbstr κs Γ Γ' α α'
              × isTypedℒHM (μs ⊩ (Γ) ⊢ α) te₀
              × isTypedℒHM (νs ⊩ (α' ∷ Γ') ⊢ β) te₁
-- //
-- [Proof]
-- | By definition [].
inv-slet (slet x x₁ x₂) = _ , _ , _ , _ , _ , x , x₁ , x₂
-- //

-- [Proposition]
-- | Assuming the induction hypothesis, the /slet/ case is
--   typecheckable with an initial typing instance.

-- //

-- [Proof]
-- | Let [..], [..], [..], [..] be the input of the
--   algorithm.
module typecheck-slet {μsᵤ : ℒHMTypes} {k : ♮ℕ} {Q : ℒHMQuant k} (Γ : ℒHMCtx Q μsᵤ) where

  -- | Furthermore, assume we have the terms [..] and [..].
  module _ (te : UntypedℒHM k) (se : UntypedℒHM (tt ∷ k)) where



    -- | First, the algorithm computes the typing for |te|,
    --   thus we assume that there is such a typing instance.
    module Success-te (𝑇-te! : InitialCtxTypingInstance Γ te) where

      open Σ 𝑇-te! renaming
        ( fst to 𝑇-te
        ; snd to Ω₀
        )

      open CtxTypingInstance 𝑇-te renaming
        ( metas to νs₀ₐ
        ; typeMetas to νs₀ₓ
        ; ctx to Γ₀
        ; typ to αᵇ₀
        ; isInstance to Γ<Γ₀
        ; hasType to Γ₀⊢αᵇ₀
        )
      -- (νs₀ₐ / νs₀ₓ ⊩ Γ₀ , αᵇ₀ , Γ<Γ₀ , Γ₀⊢αᵇ₀)

      -- | Once we have typechecked te, we know that νs₀ₓ are the
      --   variables over which the type αᵇ₀ is quantified
      --   thus the context in which we typecheck `se` is the following
      α₀Γ₀ : ℒHMCtx (νs₀ₓ ∷' Q) νs₀ₐ
      α₀Γ₀ = αᵇ₀ ∷ Γ₀

      σᵃᵤ₀ = fst Γ<Γ₀

      -- | With this context we typecheck |se|, thus let us assume
      --   that there is such a typing instance [....]
      module Success-se (𝑇-se! : InitialCtxTypingInstance (α₀Γ₀) se) where

        open Σ 𝑇-se! renaming
          ( fst to 𝑇-se
          ; snd to Ω₁
          )

        open CtxTypingInstance 𝑇-se renaming
          ( metas to νs₁ₐ
          ; typeMetas to νs₁ₓ
          ; ctx to Δ
          ; typ to βᵇ₁
          ; isInstance to α₀Γ₀<Δ
          ; hasType to Δ⊢βᵇ₁
          )
        -- (νs₁ₐ / νs₁ₓ ⊩ Δ , βᵇ₁ , α₀Γ₀<Δ , Δ⊢βᵇ₁)
        -- module _ (((νs₁ₐ / νs₁ₓ ⊩ α₁Γ₁ , βᵇ₁ , α₀Γ₀<α₁Γ₁ , α₁Γ₁⊢βᵇ₁), Ω₁) : InitialCtxTypingInstance (α₀Γ₀) se) where

        -- | Since we know that |Δ| has the same quantifications as |α₀Γ₀|,
        --   we also know that it splits into [..] and [..].
        α₁ = split-Listᴰ² Δ .fst
        Γ₁ = split-Listᴰ² Δ .snd

        -- | Call this one
        α₁Γ₁ : ℒHMCtx (νs₀ₓ ∷' Q) νs₁ₐ
        α₁Γ₁ = α₁ ∷ Γ₁

        -- | And we have actually [..] [] [].
        lem-00 : Δ ≡ α₁Γ₁
        lem-00 with Δ
        ... | (α₁ ∷ Γ₁) = refl-≡

        -- | We can restore the typing judgement to this context, i.e., we have
        α₁Γ₁⊢βᵇ₁ : isTypedℒHM ((νs₁ₐ ⊔ νs₁ₓ) ⊩ (α₁Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ βᵇ₁) se
        α₁Γ₁⊢βᵇ₁ = Δ⊢βᵇ₁
                   ⟪ transp-isTypedℒHM (cong (_⇃[ ι₀ ]⇂ᶜ) lem-00) refl-≡ ⟫

        -- | We have the following facts.
        Γ₀<Γ₁ : Γ₀ <Γ Γ₁
        Γ₀<Γ₁ = record { fst = α₀Γ₀<Δ .fst ; snd = λ i -> split-Listᴰ² (snd α₀Γ₀<Δ i) .snd  }

        σᵃ₀₁ = fst Γ₀<Γ₁

        α₁' : ℒHMType ⟨ νs₁ₐ ⊔ νs₁ₓ ⊔ νs₀ₓ ⟩
        α₁' = (α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂)

        lem-1a : αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ id ]⇂ ≡ α₁
        lem-1a = λ i -> split-Listᴰ² (α₀Γ₀<Δ .snd i) .fst

        lem-1b : Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ≡ Γ₁
        lem-1b = λ i -> split-Listᴰ² (α₀Γ₀<Δ .snd i) .snd

        -- | And this typing judgement.
        -- abstract
        Γ₁⊢α₁' : isTypedℒHM (νs₁ₐ ⊔ νs₁ₓ ⊔ νs₀ₓ ⊩ Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⊢ α₁') te
        Γ₁⊢α₁' = Γ₀⊢αᵇ₀
                  >> isTypedℒHM ((νs₀ₐ ⊔ νs₀ₓ) ⊩ (Γ₀ ⇃[ ι₀ ]⇂ᶜ) ⊢ αᵇ₀) te <<

                  ⟪ §-isTypedℒHM.prop-4 {Γ = Γ₀} σᵃ₀₁ id ⟫

                  >> isTypedℒHM (_ ⊩ (Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ id ]⇂) te <<

                  ⟪ transp-isTypedℒHM (cong _⇃[ ι₀ ]⇂ᶜ lem-1b) lem-1a ⟫

                  >> isTypedℒHM (_ ⊩ (Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₁ ) te <<

                  ⟪ §-isTypedℒHM.prop-4 {Γ = Γ₁} ι₀ id ⟫

                  >> isTypedℒHM (_ ⊩ (Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ) te <<

                  ⟪ transp-isTypedℒHM (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₁}) refl-≡ ⟫

                  >> isTypedℒHM (_ ⊩ (Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) ⊢ α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ) te <<



        -- | And this lemma.
        lem-2 : Γ₁ ⇃[ ι₀ {b = νs₁ₓ} ◆ ι₀ {b = νs₀ₓ} ]⇂ᶜ ⇃[ ⟨ refl-≅ ⟩ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
        lem-2 = trans-Path (functoriality-id-⇃[]⇂ᶜ) (sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₁}))

        -- | And something is an abstraction.
        isAb : isAbstr νs₀ₓ (Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) (Γ₁ ⇃[ ι₀ ]⇂ᶜ) α₁' (α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂)
        isAb = record { metasProof = refl-≅ ; ctxProof = lem-2 ; typeProof = functoriality-id-⇃[]⇂ }


        -- | And this together gives us this typing instance.
        𝑇 : CtxTypingInstance Γ (slet te se)
        𝑇 = νs₁ₐ / νs₁ₓ ⊩ Γ₁ , βᵇ₁ , Γ<Γ₀ ⟡ Γ₀<Γ₁ , (slet isAb Γ₁⊢α₁' α₁Γ₁⊢βᵇ₁)


        -- | Now assume we are given another typing instance.
        module _ (𝑆 : CtxTypingInstance Γ (slet te se)) where
          open CtxTypingInstance 𝑆 renaming
            ( metas to νs₃ₐ
            ; typeMetas to νs₃ₓ
            ; ctx to Γ₃
            ; typ to β₃
            ; isInstance to Γ<Γ₃
            ; hasType to Γ₃⊢slettese
            )
          -- (νs₃ₐ / νs₃ₓ ⊩ Γ₃ , β₃ , Γ<Γ₃ , Γ₃⊢slettese)


          -- | We know that since we have a typing instance |Γ₃ ⊢ slet te se : β₃|,
          --   there must be [..].
          invR = inv-slet Γ₃⊢slettese
          νs₂ = invR .fst
          νs₃ₓ₊ = invR .snd .fst
          Γ₂ = invR .snd .snd .fst
          α₂ = invR .snd .snd .snd .fst
          α₃ = invR .snd .snd .snd .snd .fst
          isAb₂ = invR .snd .snd .snd .snd .snd .fst
          Γ₂⊢α₂ = invR .snd .snd .snd .snd .snd .snd .fst
          α₃Γ₃⊢β₃ = invR .snd .snd .snd .snd .snd .snd .snd

          -- slet {μs = νs₂} {κs = νs₃ₓ₊} {Γ = Γ₂} {α = α₂} {α' = α₃}  isAb₂ Γ₂⊢α₂ α₃Γ₃⊢β₃

          σ₂₃₊ : νs₂ ≅ νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊
          σ₂₃₊ = metasProof isAb₂

          あ : ((νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊) ≅ (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))
          あ = assoc-l-⊔-ℒHMTypes

          α₃' : ℒHMType ⟨(νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))⟩
          α₃' = α₃ ⇃[ ⟨ あ ⟩ ]⇂

          -- | We have this lemma.
          module lem-11 where abstract
            Proof : isTypedℒHM (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te
            Proof = Γ₂⊢α₂
                  >> isTypedℒHM (νs₂ ⊩ Γ₂ ⊢ α₂) te <<
                  ⟪ §-isTypedℒHM.prop-2 ⟨ σ₂₃₊ ⟩ ⟫
                  >> isTypedℒHM (_ ⊩ Γ₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂ᶜ ⊢ α₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂) te <<
                  ⟪ transp-isTypedℒHM (trans-Path (ctxProof isAb₂) (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₃})) (typeProof isAb₂) ⟫
                  >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⊢ α₃) te <<
                  ⟪ §-isTypedℒHM.prop-2 ⟨ あ ⟩ ⟫
                  >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ あ ⟩ ]⇂ᶜ ⊢ α₃ ⇃[ ⟨ あ ⟩ ]⇂) te <<
                  ⟪ transp-isTypedℒHM (trans-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₃}) (Γ₃ ⇃[≀ §-assoc-l-⊔'.prop-1 ≀]⇂ᶜ)) refl-≡ ⟫
                  >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te <<

          -- | And we call this one.
          module Ω₀R where abstract
            Proof : (νs₀ₐ / νs₀ₓ ⊩ Γ₀ , αᵇ₀ , Γ<Γ₀ , Γ₀⊢αᵇ₀) <TI ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11.Proof)
            Proof = Ω₀ ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11.Proof)


          σᵃ₀₃ : νs₀ₐ ⟶ νs₃ₐ
          σᵃ₀₃ = tiSubₐ Ω₀R.Proof

          σˣ₀₃ : νs₀ₓ ⟶ νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊)
          σˣ₀₃ = tiSubₓ Ω₀R.Proof

          α₀' = αᵇ₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂

          module lem-14 where abstract
            sublem-01 : σᵃ₀₃ ◆ (ι₀ ◆ ι₀) ∼ σᵃ₀₃ ◆ ι₀ ◆ ⟨ あ ⟩⁻¹
            sublem-01 = (refl ◈ §-assoc-l-⊔'.prop-1') ∙ assoc-r-◆

            Proof : ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ≣ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹
            Proof = ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘        ⟨ ⦗≀ sublem-01 , refl ≀⦘ ⟩-∼
                    ⦗ σᵃ₀₃ ◆ ι₀ ◆ ⟨ あ ⟩⁻¹ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘  ⟨ append-⦗⦘ ⁻¹ ⟩-∼
                    ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹            ∎

          module lem-15 where abstract
            Proof : α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ≡ α₃
            Proof = α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂         ⟨ functoriality-◆-⇃[]⇂ {τ = α₀'} ⟩-≡
                    α₀' ⇃[ (ι₀ ⇃⊔⇂ id) ◆ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂           ⟨ α₀' ⇃[≀ append-⇃⊔⇂ ≀]⇂ ⟩-≡
                    α₀' ⇃[ ⦗ ι₀ ◆ ι₀ , id ◆ (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⦘ ]⇂             ⟨ α₀' ⇃[≀ ⦗≀ refl , unit-l-◆ ≀⦘ ≀]⇂ ⟩-≡
                    α₀' ⇃[ ⦗ ι₀ ◆ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂                    ⟨ functoriality-◆-⇃[]⇂ {τ = αᵇ₀} ⟩-≡
                    αᵇ₀ ⇃[ (σᵃ₀₃ ⇃⊔⇂ id) ◆ ⦗ ι₀ ◆ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂    ⟨ αᵇ₀ ⇃[≀ append-⇃⊔⇂ ≀]⇂ ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , id ◆ (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⦘ ]⇂    ⟨ αᵇ₀ ⇃[≀ ⦗≀ refl , unit-l-◆ ≀⦘ ≀]⇂ ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⦘ ]⇂         ⟨ αᵇ₀ ⇃[≀ lem-14.Proof ≀]⇂ ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹ ]⇂                  ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = αᵇ₀}) ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ]⇂ ⇃[ ⟨ あ ⟩⁻¹ ]⇂              ⟨ cong _⇃[ ⟨ あ ⟩⁻¹ ]⇂ (typProof Ω₀R.Proof) ⟩-≡
                    α₃' ⇃[ ⟨ あ ⟩⁻¹ ]⇂                                         ⟨ functoriality-◆-⇃[]⇂ {τ = α₃} ⟩-≡
                    α₃  ⇃[ ⟨ あ ⟩ ◆ ⟨ あ ⟩⁻¹ ]⇂                                ⟨ α₃ ⇃[≀ inv-r-◆ (of あ) ≀]⇂ ⟩-≡
                    α₃  ⇃[ id ]⇂                                               ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                    α₃                                                         ∎-≡

          abstract
            lem-20 : isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ ((α₀' ∷ Γ₃) ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
            lem-20 = α₃Γ₃⊢β₃
                  >> isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (α₃ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                  ⟪ transp-isTypedℒHM ((λ i -> lem-15.Proof (~ i) ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ))) refl-≡ ⟫
                  >> isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                  ⟪ §2-isTypedℒHM.prop-2 {α = α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂} (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⟫
                  >> isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<

          α₀Γ₀<α₀'Γ₃ :  α₀Γ₀ <Γ (α₀' ∷ Γ₃)
          α₀Γ₀<α₀'Γ₃ = record { fst = σᵃ₀₃ ; snd = λ i -> α₀' ∷ ctxProofTI Ω₀R.Proof i }


          -- | Then, call this.
          module Ω₁R where abstract
            Proof : (νs₁ₐ / νs₁ₓ ⊩ Δ , βᵇ₁ , α₀Γ₀<Δ , Δ⊢βᵇ₁) <TI (νs₃ₐ / νs₃ₓ ⊩ α₀' ∷ Γ₃ , β₃ , α₀Γ₀<α₀'Γ₃ , lem-20)
            Proof = Ω₁ (νs₃ₐ / νs₃ₓ ⊩ α₀' ∷ Γ₃ , β₃ , α₀Γ₀<α₀'Γ₃ , lem-20)

          σᵃ₁₃ : νs₁ₐ ⟶ νs₃ₐ
          σᵃ₁₃ = tiSubₐ Ω₁R.Proof

          σˣ₁₃ : νs₁ₓ ⟶ (νs₃ₐ ⊔ νs₃ₓ)
          σˣ₁₃ = tiSubₓ Ω₁R.Proof

          lem-30 : βᵇ₁ ⇃[ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘ ]⇂ ≡ β₃
          lem-30 = typProof Ω₁R.Proof

          -- | The final equation chain.
          lem-40 : σᵃᵤ₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃ ∼ fst Γ<Γ₃
          lem-40 = σᵃᵤ₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃   ⟨ assoc-l-◆ ⟩-∼
                   σᵃᵤ₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₃) ⟨ refl {a = σᵃᵤ₀} ◈ subProof Ω₁R.Proof ⟩-∼
                   σᵃᵤ₀ ◆ σᵃ₀₃          ⟨ subProof Ω₀R.Proof ⟩-∼
                   fst Γ<Γ₃             ∎

          -- | All together we see that [..], by taking [....]
          lem-50 : 𝑇 <TI 𝑆
          lem-50 = record { tiSubₐ = σᵃ₁₃ ; tiSubₓ = σˣ₁₃ ; typProof = lem-30 ; subProof = lem-40 }

        Result : InitialCtxTypingInstance Γ (slet te se)
        Result = 𝑇 , lem-50


  -- | With this we are done.

      module Fail-se (¬𝑇-se : ¬ CtxTypingInstance (α₀Γ₀) se) where

        --------------------------------------
        -- BEGIN DUPLICATE CODE
        --

        module _ (𝑆 : CtxTypingInstance Γ (slet te se)) where
          open CtxTypingInstance 𝑆 renaming
            ( metas to νs₃ₐ
            ; typeMetas to νs₃ₓ
            ; ctx to Γ₃
            ; typ to β₃
            ; isInstance to Γ<Γ₃
            ; hasType to Γ₃⊢slettese
            )
          -- (νs₃ₐ / νs₃ₓ ⊩ Γ₃ , β₃ , Γ<Γ₃ , Γ₃⊢slettese)


          -- | We know that since we have a typing instance |Γ₃ ⊢ slet te se : β₃|,
          --   there must be [..].
          invR = inv-slet Γ₃⊢slettese
          νs₂ = invR .fst
          νs₃ₓ₊ = invR .snd .fst
          Γ₂ = invR .snd .snd .fst
          α₂ = invR .snd .snd .snd .fst
          α₃ = invR .snd .snd .snd .snd .fst
          isAb₂ = invR .snd .snd .snd .snd .snd .fst
          Γ₂⊢α₂ = invR .snd .snd .snd .snd .snd .snd .fst
          α₃Γ₃⊢β₃ = invR .snd .snd .snd .snd .snd .snd .snd

          -- slet {μs = νs₂} {κs = νs₃ₓ₊} {Γ = Γ₂} {α = α₂} {α' = α₃}  isAb₂ Γ₂⊢α₂ α₃Γ₃⊢β₃

          σ₂₃₊ : νs₂ ≅ νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊
          σ₂₃₊ = metasProof isAb₂

          あ : ((νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊) ≅ (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))
          あ = assoc-l-⊔-ℒHMTypes

          α₃' : ℒHMType ⟨(νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))⟩
          α₃' = α₃ ⇃[ ⟨ あ ⟩ ]⇂

          -- | We have this lemma.
          module lem-11 where abstract
            Proof : isTypedℒHM (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te
            Proof = Γ₂⊢α₂
                  >> isTypedℒHM (νs₂ ⊩ Γ₂ ⊢ α₂) te <<
                  ⟪ §-isTypedℒHM.prop-2 ⟨ σ₂₃₊ ⟩ ⟫
                  >> isTypedℒHM (_ ⊩ Γ₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂ᶜ ⊢ α₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂) te <<
                  ⟪ transp-isTypedℒHM (trans-Path (ctxProof isAb₂) (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₃})) (typeProof isAb₂) ⟫
                  >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⊢ α₃) te <<
                  ⟪ §-isTypedℒHM.prop-2 ⟨ あ ⟩ ⟫
                  >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ あ ⟩ ]⇂ᶜ ⊢ α₃ ⇃[ ⟨ あ ⟩ ]⇂) te <<
                  ⟪ transp-isTypedℒHM (trans-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₃}) (Γ₃ ⇃[≀ §-assoc-l-⊔'.prop-1 ≀]⇂ᶜ)) refl-≡ ⟫
                  >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te <<

          -- | And we call this one.
          module Ω₀R where abstract
            Proof : (νs₀ₐ / νs₀ₓ ⊩ Γ₀ , αᵇ₀ , Γ<Γ₀ , Γ₀⊢αᵇ₀) <TI ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11.Proof)
            Proof = Ω₀ ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11.Proof)


          σᵃ₀₃ : νs₀ₐ ⟶ νs₃ₐ
          σᵃ₀₃ = tiSubₐ Ω₀R.Proof

          σˣ₀₃ : νs₀ₓ ⟶ νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊)
          σˣ₀₃ = tiSubₓ Ω₀R.Proof

          α₀' = αᵇ₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂

          module lem-14 where abstract
            sublem-01 : σᵃ₀₃ ◆ (ι₀ ◆ ι₀) ∼ σᵃ₀₃ ◆ ι₀ ◆ ⟨ あ ⟩⁻¹
            sublem-01 = (refl ◈ §-assoc-l-⊔'.prop-1') ∙ assoc-r-◆

            Proof : ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ≣ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹
            Proof = ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘        ⟨ ⦗≀ sublem-01 , refl ≀⦘ ⟩-∼
                    ⦗ σᵃ₀₃ ◆ ι₀ ◆ ⟨ あ ⟩⁻¹ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘  ⟨ append-⦗⦘ ⁻¹ ⟩-∼
                    ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹            ∎

          module lem-15 where abstract
            Proof : α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ≡ α₃
            Proof = α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂         ⟨ functoriality-◆-⇃[]⇂ {τ = α₀'} ⟩-≡
                    α₀' ⇃[ (ι₀ ⇃⊔⇂ id) ◆ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂           ⟨ α₀' ⇃[≀ append-⇃⊔⇂ ≀]⇂ ⟩-≡
                    α₀' ⇃[ ⦗ ι₀ ◆ ι₀ , id ◆ (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⦘ ]⇂             ⟨ α₀' ⇃[≀ ⦗≀ refl , unit-l-◆ ≀⦘ ≀]⇂ ⟩-≡
                    α₀' ⇃[ ⦗ ι₀ ◆ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂                    ⟨ functoriality-◆-⇃[]⇂ {τ = αᵇ₀} ⟩-≡
                    αᵇ₀ ⇃[ (σᵃ₀₃ ⇃⊔⇂ id) ◆ ⦗ ι₀ ◆ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂    ⟨ αᵇ₀ ⇃[≀ append-⇃⊔⇂ ≀]⇂ ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , id ◆ (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⦘ ]⇂    ⟨ αᵇ₀ ⇃[≀ ⦗≀ refl , unit-l-◆ ≀⦘ ≀]⇂ ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ (ι₀ ◆ ι₀) , (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⦘ ]⇂         ⟨ αᵇ₀ ⇃[≀ lem-14.Proof ≀]⇂ ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹ ]⇂                  ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = αᵇ₀}) ⟩-≡
                    αᵇ₀ ⇃[ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ]⇂ ⇃[ ⟨ あ ⟩⁻¹ ]⇂              ⟨ cong _⇃[ ⟨ あ ⟩⁻¹ ]⇂ (typProof Ω₀R.Proof) ⟩-≡
                    α₃' ⇃[ ⟨ あ ⟩⁻¹ ]⇂                                         ⟨ functoriality-◆-⇃[]⇂ {τ = α₃} ⟩-≡
                    α₃  ⇃[ ⟨ あ ⟩ ◆ ⟨ あ ⟩⁻¹ ]⇂                                ⟨ α₃ ⇃[≀ inv-r-◆ (of あ) ≀]⇂ ⟩-≡
                    α₃  ⇃[ id ]⇂                                               ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                    α₃                                                         ∎-≡

          abstract
            lem-20 : isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ ((α₀' ∷ Γ₃) ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
            lem-20 = α₃Γ₃⊢β₃
                  >> isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (α₃ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                  ⟪ transp-isTypedℒHM ((λ i -> lem-15.Proof (~ i) ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ))) refl-≡ ⟫
                  >> isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                  ⟪ §2-isTypedℒHM.prop-2 {α = α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂} (σˣ₀₃ ◆ ⟨ あ ⟩⁻¹) ⟫
                  >> isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<

          α₀Γ₀<α₀'Γ₃ :  α₀Γ₀ <Γ (α₀' ∷ Γ₃)
          α₀Γ₀<α₀'Γ₃ = record { fst = σᵃ₀₃ ; snd = λ i -> α₀' ∷ ctxProofTI Ω₀R.Proof i }

          --
          -- END DUPLICATE CODE
          --------------------------------------

          Result : 𝟘-𝒰
          Result = ¬𝑇-se (νs₃ₐ / νs₃ₓ ⊩ α₀' ∷ Γ₃ , β₃ , α₀Γ₀<α₀'Γ₃ , lem-20)


    module Fail-te (¬𝑇-te : ¬ CtxTypingInstance Γ te) where

      --------------------------------------
      -- BEGIN DUPLICATE CODE
      --

      module _ (𝑆 : CtxTypingInstance Γ (slet te se)) where
        open CtxTypingInstance 𝑆 renaming
          ( metas to νs₃ₐ
          ; typeMetas to νs₃ₓ
          ; ctx to Γ₃
          ; typ to β₃
          ; isInstance to Γ<Γ₃
          ; hasType to Γ₃⊢slettese
          )
        -- (νs₃ₐ / νs₃ₓ ⊩ Γ₃ , β₃ , Γ<Γ₃ , Γ₃⊢slettese)


        -- | We know that since we have a typing instance |Γ₃ ⊢ slet te se : β₃|,
        --   there must be [..].
        invR = inv-slet Γ₃⊢slettese
        νs₂ = invR .fst
        νs₃ₓ₊ = invR .snd .fst
        Γ₂ = invR .snd .snd .fst
        α₂ = invR .snd .snd .snd .fst
        α₃ = invR .snd .snd .snd .snd .fst
        isAb₂ = invR .snd .snd .snd .snd .snd .fst
        Γ₂⊢α₂ = invR .snd .snd .snd .snd .snd .snd .fst
        α₃Γ₃⊢β₃ = invR .snd .snd .snd .snd .snd .snd .snd

        -- slet {μs = νs₂} {κs = νs₃ₓ₊} {Γ = Γ₂} {α = α₂} {α' = α₃}  isAb₂ Γ₂⊢α₂ α₃Γ₃⊢β₃

        σ₂₃₊ : νs₂ ≅ νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊
        σ₂₃₊ = metasProof isAb₂

        あ : ((νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊) ≅ (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))
        あ = assoc-l-⊔-ℒHMTypes

        α₃' : ℒHMType ⟨(νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))⟩
        α₃' = α₃ ⇃[ ⟨ あ ⟩ ]⇂

        -- | We have this lemma.
        module lem-11 where abstract
          Proof : isTypedℒHM (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te
          Proof = Γ₂⊢α₂
                >> isTypedℒHM (νs₂ ⊩ Γ₂ ⊢ α₂) te <<
                ⟪ §-isTypedℒHM.prop-2 ⟨ σ₂₃₊ ⟩ ⟫
                >> isTypedℒHM (_ ⊩ Γ₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂ᶜ ⊢ α₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂) te <<
                ⟪ transp-isTypedℒHM (trans-Path (ctxProof isAb₂) (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₃})) (typeProof isAb₂) ⟫
                >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⊢ α₃) te <<
                ⟪ §-isTypedℒHM.prop-2 ⟨ あ ⟩ ⟫
                >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ あ ⟩ ]⇂ᶜ ⊢ α₃ ⇃[ ⟨ あ ⟩ ]⇂) te <<
                ⟪ transp-isTypedℒHM (trans-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₃}) (Γ₃ ⇃[≀ §-assoc-l-⊔'.prop-1 ≀]⇂ᶜ)) refl-≡ ⟫
                >> isTypedℒHM (_ ⊩ Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te <<

        --
        -- END DUPLICATE CODE
        --------------------------------------

        Result : 𝟘-𝒰
        Result = ¬𝑇-te ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11.Proof)

-- //

