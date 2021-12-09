
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.App where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition

open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad

-- open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.Iso renaming (_≅_ to _≅ᵘ_ ; ⟨_⟩⁻¹ to ⟨_⟩⁻¹ᵘ)
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition using (append-⦗⦘ ; ⦗≀_≀⦘)
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2

open import Verification.Core.Order.Preorder

open Overwrite:isCategory:⧜𝒯⊔Term 𝒹
open Overwrite:isCoproduct:⧜𝒯⊔Term 𝒹
open Overwrite:hasCoproducts:⧜𝒯⊔Term 𝒹
open Overwrite:hasFiniteCoproducts:⧜𝒯⊔Term 𝒹
open Overwrite:hasInitial:⧜𝒯⊔Term 𝒹
open Overwrite:isInitial:⧜𝒯⊔Term 𝒹


private
  _⟶_ = Hom

  _≅_ = _≅ᵘ_ {𝒞 = ⧜𝒯⊔Term 𝒹} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}}
  ⟨_⟩⁻¹ = ⟨_⟩⁻¹ᵘ {𝒞 = ⧜𝒯⊔Term 𝒹} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}}

-- {-# DISPLAY isCoequalizer.π₌ _ = π #-}
-- {-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
-- {-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = f ◆ g #-}
{-# DISPLAY 内id-⧜𝐒𝐮𝐛𝐬𝐭 = id #-}


private
  instance
    hasSplitEpiMonoFactorization:ℒHMTypes : hasSplitEpiMonoFactorization ℒHMTypes
    hasSplitEpiMonoFactorization:ℒHMTypes = {!!}

  assoc-l-⊔-ℒHMTypes : ∀{a b c : ℒHMTypes} -> (a ⊔ b) ⊔ c ≅ a ⊔ (b ⊔ c)
  assoc-l-⊔-ℒHMTypes = {!!}


-- [Lemma]
-- | "Inversion of App"

inv-app : ∀{k μs} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μs} {β : ℒHMType ⟨ μs ⟩}
           --------------------------------------
           -- constructor inputs
           -> {te : UntypedℒHM k}
           -> {se : UntypedℒHM k}
           --------------------------------------
           -- condition: is typed
           -> isTypedℒHM (μs ⊩ (Q , Γ) ⊢ β) (app te se)
           --------------------------------------
           -- result: we have a lot
           -> ∑ λ (α : ℒHMType ⟨ μs ⟩)
           -> isTypedℒHM (μs ⊩ (Q , Γ) ⊢ α ⇒ β) te
             ×-𝒰 isTypedℒHM (μs ⊩ (Q , Γ) ⊢ α) se
inv-app (app x x₁) = _ , (x , x₁)

-- //






-- [Proof]
-- | Let [..], [..], [..], [..] be the input of the
--   algorithm.
module typecheck-app {νsₐ : ℒHMTypes} {k : ♮ℕ} {Q : ℒHMQuant k} (Γ : ℒHMCtxFor Q νsₐ) where

  -- | Furthermore, assume we have the terms [..] and [..].
  module _ (te : UntypedℒHM k) (se : UntypedℒHM k) where


    -- | First the algorithm computes the typing for |te|,
    --   thus we assume that there is such a typing instance.
    module _ (𝑇-te! : InitialCtxTypingInstance Γ te) where

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

      -- | Next use this context to typecheck the term |se|.
      module _ (𝑇-se! : InitialCtxTypingInstance Γ₀ se) where

        open Σ 𝑇-se! renaming
          ( fst to 𝑇-se
          ; snd to Ω₁
          )

        open CtxTypingInstance 𝑇-se renaming
          ( metas to νs₁ₐ
          ; typeMetas to νs₁ₓ
          ; ctx to Γ₁
          ; typ to βᵇ₁
          ; isInstance to Γ₀<Γ₁
          ; hasType to Γ₁⊢βᵇ₁
          )

        νs = νsₐ


        σᵃᵤ₀ : _ ⟶ νs₀ₐ
        σᵃᵤ₀ = fst Γ<Γ₀

        -- lift the τ0 typing to Γ₁
        σᵃ₀₁ : νs₀ₐ ⟶ νs₁ₐ
        σᵃ₀₁ = fst Γ₀<Γ₁

        σᵃᵤ₁ : νsₐ ⟶ νs₁ₐ
        σᵃᵤ₁ = σᵃᵤ₀ ◆ σᵃ₀₁

        νs₀ = νs₀ₐ ⊔ νs₀ₓ

        σᵤ₀ : νs ⟶ νs₀
        σᵤ₀ = σᵃᵤ₀ ◆ ι₀

        νs₁ = νs₁ₐ ⊔ (νs₀ₓ ⊔ νs₁ₓ)

        σ₀₁ : νs₀ ⟶ νs₁
        σ₀₁ = σᵃ₀₁ ⇃⊔⇂ ι₀


        -- we lift α₀ to the metas νs₁
        -- τ₀'
        α₁ : ℒHMType ⟨ νs₁ₐ ⊔ (νs₀ₓ ⊔ νs₁ₓ) ⟩
        α₁ = αᵇ₀ ⇃[ σ₀₁ ]⇂

        β₁ : ℒHMType ⟨ νs₁ₐ ⊔ (νs₀ₓ ⊔ νs₁ₓ) ⟩
        β₁ = βᵇ₁ ⇃[ id ⇃⊔⇂ ι₁ ]⇂

        -- we need a new type variable for the return
        -- type of the application, so we move to νs₂
        νs₂ₐ = νs₁ₐ
        νs₂ = νs₂ₐ ⊔ (νs₀ₓ ⊔ νs₁ₓ ⊔ st)

        σ₁₂ : νs₁ ⟶ νs₂
        σ₁₂ = id ⇃⊔⇂ ι₀

        -- σᵤ₂ : νs ⟶ νs₂
        -- σᵤ₂ = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂

        α₂ : ℒHMType ⟨ νs₂ₐ ⊔ (νs₀ₓ ⊔ νs₁ₓ ⊔ st) ⟩
        α₂ = α₁ ⇃[ σ₁₂ ]⇂

        β₂ : ℒHMType ⟨ νs₂ ⟩
        β₂ = β₁ ⇃[ σ₁₂ ]⇂


        -- Γ₂ = Γ₁ ⇃[ σ₁₂ ]⇂ᶜ
        Γ₂ = Γ₁

        -- we call the new type γ
        γᵇₜ : ℒHMType ⟨ st ⟩
        γᵇₜ = var incl

        γ₂ : ℒHMType ⟨ νs₂ ⟩
        γ₂ = γᵇₜ ⇃[ ι₁ ◆ ι₁ ]⇂

        -- the types which we unify are:
        u : ℒHMType ⟨ νs₂ ⟩
        u = α₂

        v : ℒHMType ⟨ νs₂ ⟩
        v = β₂ ⇒ γ₂


        -- | Now assume we have the coeq.
        module _ (x : hasCoequalizer (asArr u) (asArr v)) where

          -- we now have the coequalizer `π₌`,
          -- but we need to factorize the map ι₀ ◆ π
          π : νs₂ ⟶ ⟨ x ⟩
          π = π₌ {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}} {{of x}}

          f : νs₂ₐ ⟶ ⟨ x ⟩
          f = ι₀ ◆ π

          factor:f : isSplitEpiMonoFactorizable f
          factor:f = factorize {{_}} {{hasSplitEpiMonoFactorization:ℒHMTypes}} f

          νs₃ₐ νs₃ₓ νs₃ : ℒHMTypes
          νs₃ₐ = image factor:f
          νs₃ₓ = rest factor:f

          νs₃ = νs₃ₐ ⊔ νs₃ₓ

          σ₂₃ : νs₂ ⟶ νs₃
          σ₂₃ = π ◆ ⟨ splitting factor:f ⟩⁻¹

          ϕ : νs₃ ≅ ⟨ x ⟩
          ϕ = splitting factor:f

          σᵃ₂₃ : νs₂ₐ ⟶ νs₃ₐ
          σᵃ₂₃ = epiHom factor:f

          β₃ = β₂ ⇃[ σ₂₃ ]⇂
          γ₃ = γ₂ ⇃[ σ₂₃ ]⇂
          Γ₃ = Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ

          lem-0 : ι₀ ◆ σ₂₃ ∼ σᵃ₂₃ ◆ ι₀
          lem-0 = {!!}

          -- thus the full substitution we need is the following
          -- σᵤ₃ = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂ ◆ σ₂₃

          Γ₂<Γ₃ : Γ₂ <Γ Γ₃
          Γ₂<Γ₃ = record { fst = σᵃ₂₃ ; snd = refl-≡ }

          Γ<Γ₃ : Γ <Γ Γ₃
          Γ<Γ₃ = Γ<Γ₀ ⟡ Γ₀<Γ₁ ⟡ Γ₂<Γ₃


          -- we know that under `σ₂₃` both α₂ and `β₂ ⇒ γ₂` are the same
          module lem-5 where abstract
            Proof : α₂ ⇃[ σ₂₃ ]⇂ ≡ (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂
            Proof = {!!}
            {-
            Proof = α₂ ⇃[ π ◆ ⟨ splitting factor:f ⟩⁻¹ ]⇂      ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α₂} {f = π} {⟨ splitting factor:f ⟩⁻¹}) ⟩-≡
                  -- α₂ ⇃[ π ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂  ⟨ cong _⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ lem-5b ⟩-≡
                  α₂ ⇃[ π ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂  ⟨ cong _⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ ? ⟩-≡
                  (β₂ ⇒ γ₂) ⇃[ π ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ ⟨ functoriality-◆-⇃[]⇂ {τ = β₂ ⇒ γ₂} {f = π} {⟨ splitting factor:f ⟩⁻¹} ⟩-≡
                  (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂                              ∎-≡
                  -}

            --   where
            --     lem-5a : (asArr α₂) ◆ π ∼ (asArr (β₂ ⇒ γ₂)) ◆ π
            --     lem-5a = ? -- equate-π₌ {{_}} {{of x}}

            --     lem-5a' : ((asArr α₂) ◆-⧜𝐒𝐮𝐛𝐬𝐭 π) ∼ ((asArr (β₂ ⇒ γ₂)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 π)
            --     lem-5a' = ? -- (abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭 ∙-≣ lem-5a) ∙-≣ (sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭)

            --     lem-5b : α₂ ⇃[ π ]⇂ ≡ (β₂ ⇒ γ₂) ⇃[ π ]⇂
            --     lem-5b = ?
                        --  let x = lem-5a'
                        --      y = cong-Str ⟨_⟩ x
                        --      z = cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 y
                        --      q = ≡-Str→≡ z

                        --      -- here: substitution of st term is st value
                        -- in ?

          module lem-6 where abstract
            Proof : Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ ≡ Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
            Proof = Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ₂} {f = ι₀} {σ₂₃} ⟩-≡
                  Γ₂ ⇃[ ι₀ ◆ σ₂₃ ]⇂ᶜ       ⟨ Γ₂ ⇃[≀ lem-0 ≀]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path (functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ₂}) ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ∎-≡

          -------------
          -- lift the typing of se and te to νs₃

          module sp₃ where abstract
            Proof : isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
            Proof = Γ₁⊢βᵇ₁
                >> isTypedℒHM (νs₁ₐ ⊔ νs₁ₓ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ βᵇ₁) se <<
                ⟪ §-isTypedℒHM.prop-3 {Γ = Γ₁} ι₁ ⟫
                >> isTypedℒHM (νs₁ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₁) se <<
                ⟪ §-isTypedℒHM.prop-3 {Γ = Γ₁} ι₀ ⟫
                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₁ ⇃[ id ⇃⊔⇂ ι₀ ]⇂) se <<
                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₂) se <<
                ⟪ §-isTypedℒHM.prop-2 {Γ = _ , Γ₂ ⇃[ ι₀ ]⇂ᶜ} {τ = β₂} σ₂₃ ⟫
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ) ⊢ β₂ ⇃[ σ₂₃ ]⇂) se <<
                ⟪ transp-isTypedℒHM lem-6.Proof refl-≡ ⟫
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₂ ⇃[ σ₂₃ ]⇂) se <<
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se <<

          module tp₃ where abstract
            Proof : isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ (β₃ ⇒ γ₃)) te
            Proof = Γ₀⊢αᵇ₀

                >> isTypedℒHM (νs₀ ⊩ (_ , Γ₀ ⇃[ ι₀ ]⇂ᶜ ) ⊢ αᵇ₀ ) te <<

                ⟪ §-isTypedℒHM.prop-4 {Γ = Γ₀} σᵃ₀₁ ι₀ ⟫

                >> isTypedℒHM (νs₁ ⊩ (_ , Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ) ⊢ αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ ι₀ ]⇂) te <<

                ⟪ transp-isTypedℒHM (cong _⇃[ ι₀ ]⇂ᶜ (Γ₀<Γ₁ .snd)) refl-≡ ⟫

                >> isTypedℒHM (νs₁ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ ) ⊢ α₁ ) te <<

                ⟪ §-isTypedℒHM.prop-3 {Γ = Γ₁} ι₀ ⟫

                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ ) ⊢ α₁ ⇃[ id ⇃⊔⇂ ι₀ ]⇂) te <<
                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ ) ⊢ α₂) te <<

                ⟪ §-isTypedℒHM.prop-2 σ₂₃ ⟫

                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ) ⊢ α₂ ⇃[ σ₂₃ ]⇂) te <<

                ⟪ transp-isTypedℒHM lem-6.Proof lem-5.Proof ⟫

                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂) te <<
                ⟪ {!!} ⟫
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃ ⇒ γ₃) te <<

          -- this shows that we do have the typing instance
          𝑇 : CtxTypingInstance Γ (app te se)
          𝑇 = νs₃ₐ / νs₃ₓ ⊩ Γ₃ , γ₃ , Γ<Γ₃ , (app tp₃.Proof sp₃.Proof)

          -- | Now we want to show that this is the initial typing instance.
          -- | > Assume we are given another typing instance.
          module _ (𝑆 : CtxTypingInstance Γ (app te se)) where
            open CtxTypingInstance 𝑆 renaming
              ( metas to νs₄ₐ
              ; typeMetas to νs₄ₓ
              ; ctx to Ξ
              ; typ to ζ₄
              ; isInstance to Γ<Ξ
              ; hasType to Ξ⊢ζ₄
              )


            -- | We know that the lam typing must have been derived by the
            --   app rule.
            inR = inv-app Ξ⊢ζ₄
            ξ₄ = inR .fst
            Ξ⊢ξ⇒ζ = inR .snd .fst
            Ξ⊢ξ = inR .snd .snd
            -- α₃⇒β₃=δ₃ = inR .snd .snd .fst
            -- Γ₃α₃⊢β₃ = inR .snd .snd .snd



            νs₄ : ℒHMTypes
            νs₄ = νs₄ₐ ⊔ νs₄ₓ

            σᵃᵤ₄ : νs ⟶ νs₄ₐ
            σᵃᵤ₄ = fst Γ<Ξ

            module ΩR₀ where abstract
              Proof : 𝑇-te <TI (νs₄ₐ / νs₄ₓ ⊩ Ξ , ((ξ₄ ⇒ ζ₄)) , Γ<Ξ , Ξ⊢ξ⇒ζ)
              Proof = Ω₀ (νs₄ₐ / νs₄ₓ ⊩ Ξ , ((ξ₄ ⇒ ζ₄)) , Γ<Ξ , Ξ⊢ξ⇒ζ)

            σᵃ₀₄ : νs₀ₐ ⟶ νs₄ₐ
            σᵃ₀₄ = tiSubₐ ΩR₀.Proof

            σˣ₀₄ : νs₀ₓ ⟶ νs₄ₐ ⊔ νs₄ₓ
            σˣ₀₄ = tiSubₓ ΩR₀.Proof

            Γ₀<Ξ : Γ₀ <Γ Ξ
            Γ₀<Ξ = record { fst = σᵃ₀₄ ; snd = ctxProofTI ΩR₀.Proof }

            module ΩR₁ where abstract
              Proof : 𝑇-se <TI (νs₄ₐ / νs₄ₓ ⊩ Ξ , ξ₄ , Γ₀<Ξ , Ξ⊢ξ)
              Proof = Ω₁ (νs₄ₐ / νs₄ₓ ⊩ Ξ , ξ₄ , Γ₀<Ξ , Ξ⊢ξ)

            σᵃ₁₄ : νs₁ₐ ⟶ νs₄ₐ
            σᵃ₁₄ = tiSubₐ ΩR₁.Proof

            σˣ₁₄ : νs₁ₓ ⟶ νs₄ₐ ⊔ νs₄ₓ
            σˣ₁₄ = tiSubₓ ΩR₁.Proof


            -------
            -- we can build a substitution from νs₂ by mapping γ to ζ₄
            -- {}
            σₜ₄ : st ⟶ νs₄
            σₜ₄ = ⧜subst (incl ζ₄)

            σ₂₄ : νs₂ ⟶ νs₄
            σ₂₄ = ⦗ σᵃ₁₄ ◆ ι₀ , ⦗ ⦗ σˣ₀₄ , σˣ₁₄ ⦘ , σₜ₄ ⦘ ⦘ -- ⦗ σ₁₄ , σₜ₄ ⦘
            -- {}
            ------

            -- we know that under this substitution,
            -- u = α₂ and v = β₂ ⇒ γ₂ become both ξ⇒ζ

            module lem-11 where abstract
              Proof : u ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
              Proof = αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ ι₀ ]⇂ ⇃[ id ⇃⊔⇂ ι₀ ]⇂ ⇃[ σ₂₄ ]⇂     ⟨ {!!} ⟩-≡
                      αᵇ₀ ⇃[ ⦗ σᵃ₀₁ ◆ σᵃ₁₄ ◆ ι₀ , σˣ₀₄ ⦘ ]⇂             ⟨ {!!} ⟩-≡
                      αᵇ₀ ⇃[ ⦗ σᵃ₀₄ ◆ ι₀ , σˣ₀₄ ⦘ ]⇂                    ⟨ typProof ΩR₀.Proof ⟩-≡
                      ξ₄ ⇒ ζ₄                                         ∎-≡

            -- we show how β₂ and γ₂ evaluate under σ₂₄
            module lem-12a where abstract
              Proof : β₂ ⇃[ σ₂₄ ]⇂ ≡ ξ₄
              Proof = βᵇ₁ ⇃[ id ⇃⊔⇂ ι₁ ]⇂ ⇃[ id ⇃⊔⇂ ι₀ ]⇂ ⇃[ σ₂₄ ]⇂   ⟨ {!!} ⟩-≡
                      βᵇ₁ ⇃[ ⦗ σᵃ₁₄ ◆ ι₀ , σˣ₁₄ ⦘ ]⇂                 ⟨ typProof ΩR₁.Proof ⟩-≡
                      ξ₄                                            ∎-≡

            module lem-12b where abstract
              Proof : γ₂ ⇃[ σ₂₄ ]⇂ ≡ ζ₄
              Proof = {!!} -- γᵇₜ ⇃[ ι₁ ◆ ι₁ ]⇂ ⇃[ σ₂₄ ]⇂           ⟨ {!!} ⟩-≡
                        -- γᵇₜ ⇃[ σₜ₄ ]⇂                         ∎-≡

            module lem-12 where abstract
              Proof : v ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
              Proof = {!!} -- λ i -> lem-12a.Proof i ⇒ lem-12b.Proof i

            -- taken together
            module lem-13 where abstract
              Proof : (asArr u) ◆ σ₂₄ ∼ (asArr v) ◆ σ₂₄
              Proof = ((sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭) ∙-≣ lem-13a) ∙-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭
                where
                  lem-13a : ((asArr u) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ₂₄) ∼ ((asArr v) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ₂₄)
                  lem-13a = {!!} -- cong-Str ⧜subst (cong-Str incl (≡→≡-Str (trans-Path lem-11.Proof (sym-Path lem-12.Proof))))


            -- ... thus we can use the universal property
            -- to get ⟨ x ⟩ ⟶ νs₄
            ε : ⟨ x ⟩ ⟶ νs₄
            ε = ⦗ σ₂₄ , {!!} ⦘₌ -- lem-13

            -- using this coequalizer derived hom, we can now build the proper
            -- 3 -> 4 morphisms

            --------------------------------------
            -- i) the "a" version
            σᵃ₃₄ : νs₃ₐ ⟶ νs₄ₐ
            σᵃ₃₄ = ι₀ ◆ ⟨ ϕ ⟩ ◆ ε ◆ ϖ₀

            module lem-20 where abstract
              Proof : σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩ ∼ ι₀ ◆ π₌
              Proof = σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩              ⟨ lem-0 ⁻¹ ◈ refl ⟩-∼
                      ι₀ ◆ σ₂₃ ◆ ⟨ ϕ ⟩               ⟨ refl ⟩-∼
                      ι₀ ◆ (π₌ ◆ ⟨ ϕ ⟩⁻¹) ◆ ⟨ ϕ ⟩    ⟨ assoc-l-◆ ∙ (refl ◈ assoc-l-◆) ⟩-∼
                      ι₀ ◆ (π₌ ◆ (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩))  ⟨ refl ◈ (refl ◈ inv-l-◆ (of ϕ)) ⟩-∼
                      ι₀ ◆ (π₌ ◆ id)                ⟨ refl ◈ unit-r-◆ ⟩-∼
                      ι₀ ◆ π₌                       ∎

            module lem-21 where abstract
              Proof : σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε ∼ σᵃ₁₄ ◆ ι₀
              Proof = σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε      ⟨ lem-20.Proof ◈ refl ⟩-∼
                      ι₀ ◆ π₌ ◆ ε                ⟨ assoc-l-◆ ⟩-∼
                      ι₀ ◆ (π₌ ◆ ε)              ⟨ refl ◈ reduce-π₌ ⟩-∼
                      ι₀ ◆ σ₂₄                   ⟨ reduce-ι₀ ⟩-∼
                      σᵃ₁₄ ◆ ι₀                  ∎

            module lem-22 where abstract
              Proof : σᵃ₂₃ ◆ σᵃ₃₄ ∼ σᵃ₁₄
              Proof = σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε ◆ ϖ₀)    ⟨ assoc-r-◆ ⟩-∼
                      (σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε)) ◆ ϖ₀  ⟨ assoc-r-◆ ◈ refl ⟩-∼
                      ((σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩)) ◆ ε) ◆ ϖ₀ ⟨ assoc-r-◆ ◈ refl ◈ refl ⟩-∼
                      (((σᵃ₂₃ ◆ ι₀) ◆ ⟨ ϕ ⟩) ◆ ε) ◆ ϖ₀ ⟨ lem-21.Proof ◈ refl ⟩-∼
                      σᵃ₁₄ ◆ ι₀ ◆ ϖ₀                  ⟨ assoc-l-◆ ⟩-∼
                      σᵃ₁₄ ◆ (ι₀ ◆ ϖ₀)                ⟨ refl ◈ reduce-ι₀ ⟩-∼
                      σᵃ₁₄ ◆ id                       ⟨ unit-r-◆ ⟩-∼
                      σᵃ₁₄                            ∎

            module lem-22b where abstract
              Proof : σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε) ∼ σᵃ₁₄ ◆ ι₀
              Proof = σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε)     ⟨ assoc-r-◆ ⟩-∼
                      ((σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩)) ◆ ε) ⟨ assoc-r-◆ ◈ refl ⟩-∼
                      (((σᵃ₂₃ ◆ ι₀) ◆ ⟨ ϕ ⟩) ◆ ε) ⟨ lem-21.Proof ⟩-∼
                      σᵃ₁₄ ◆ ι₀                  ∎

            module lem-23 where abstract
              Proof : fst Γ<Γ₃ ◆ σᵃ₃₄ ∼ σᵃᵤ₄
              Proof = (σᵃᵤ₀ ◆ σᵃ₀₁) ◆ σᵃ₂₃ ◆ σᵃ₃₄       ⟨ assoc-l-◆ ⟩-∼
                      (σᵃᵤ₀ ◆ σᵃ₀₁) ◆ (σᵃ₂₃ ◆ σᵃ₃₄)     ⟨ refl ◈ lem-22.Proof ⟩-∼
                      (σᵃᵤ₀ ◆ σᵃ₀₁) ◆ σᵃ₁₄              ⟨ assoc-l-◆ ⟩-∼
                      σᵃᵤ₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₄)              ⟨ refl ◈ subProof ΩR₁.Proof ⟩-∼
                      σᵃᵤ₀ ◆ σᵃ₀₄                       ⟨ subProof ΩR₀.Proof  ⟩-∼
                      σᵃᵤ₄                              ∎

            --------------------------------------
            -- i) the "x" version
            σˣ₃₄ : νs₃ₓ ⟶ νs₄
            σˣ₃₄ = ι₁ ◆ ⟨ ϕ ⟩ ◆ ε

            module lem-30 where abstract
              Proof : σᵃ₃₄ ◆ ι₀ ∼ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε
              Proof = cancel-epi {{_}} {{isEpi:epiHom factor:f}} lem-30a
                where
                  lem-30a : σᵃ₂₃ ◆ (σᵃ₃₄ ◆ ι₀) ∼ σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε)
                  lem-30a = σᵃ₂₃ ◆ (σᵃ₃₄ ◆ ι₀)      ⟨ assoc-r-◆ ⟩-∼
                            (σᵃ₂₃ ◆ σᵃ₃₄) ◆ ι₀      ⟨ lem-22.Proof ◈ refl ⟩-∼
                            σᵃ₁₄ ◆ ι₀               ⟨ lem-22b.Proof ⁻¹ ⟩-∼
                            σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε) ∎

            module lem-31 where abstract
              open import Verification.Core.Category.Std.Category.Notation.Associativity
              Proof : σ₂₃ ◆ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ∼ σ₂₄
              Proof = σ₂₃ ◆ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘      ⟨ refl ◈ cong-∼ {{isSetoidHom:⦗⦘}} (lem-30.Proof , refl) ⟩-∼
                      σ₂₃ ◆ ⦗ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε , σˣ₃₄ ⦘
                        ⟨ refl ◈ cong-∼ {{isSetoidHom:⦗⦘}} (assoc-l-◆ , assoc-l-◆) ⟩-∼
                      σ₂₃ ◆ ⦗ ι₀ ◆ (⟨ ϕ ⟩ ◆ ε) , (ι₁ ◆ (⟨ ϕ ⟩ ◆ ε)) ⦘
                        ⟨ refl ◈ expand-ι₀,ι₁ ⁻¹ ⟩-∼
                      (π₌ ◆ ⟨ ϕ ⟩⁻¹) ◆ (⟨ ϕ ⟩ ◆ ε)
                        ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⟩-∼
                      π₌ ◆ (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩) ◆ ε
                        ⟨ refl ◈ inv-l-◆ (of ϕ) ◈ refl ⟩-∼
                      π₌ ◆ id ◆ ε
                        ⟨ unit-r-◆ ◈ refl ⟩-∼
                      π₌ ◆ ε
                        ⟨ reduce-π₌ {{_}} {{of x}} ⟩-∼
                      σ₂₄
                        ∎

            module lem-32 where abstract
              Proof : γ₃ ⇃[ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ]⇂ ≡ ζ₄
              Proof = γ₂ ⇃[ σ₂₃ ]⇂ ⇃[ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = γ₂} {f = σ₂₃} {⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘} ⟩-≡
                      γ₂ ⇃[ σ₂₃ ◆ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ]⇂        ⟨ γ₂ ⇃[≀ lem-31.Proof ≀]⇂ ⟩-≡
                      γ₂ ⇃[ σ₂₄ ]⇂                               ⟨ lem-12b.Proof ⟩-≡
                      ζ₄                                         ∎-≡

            isInitial:𝑇 : 𝑇 <TI 𝑆
            isInitial:𝑇 = record { tiSubₐ = σᵃ₃₄ ; tiSubₓ = σˣ₃₄ ; typProof = lem-32.Proof ; subProof = lem-23.Proof }

          -- | Which means that we finally have our result [..], which is [....]

          Result : InitialCtxTypingInstance Γ (app te se)
          Result = 𝑇 , isInitial:𝑇

          -- | And we are done!

-- //

