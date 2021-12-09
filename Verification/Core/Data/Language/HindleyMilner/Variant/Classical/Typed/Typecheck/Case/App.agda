
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



-- [Proof]
-- | Let [..], [..], [..], [..] be the input of the
--   algorithm.
module typecheck-lam {νsₐ : ℒHMTypes} {k : ♮ℕ} {Q : ℒHMQuant k} (Γ : ℒHMCtxFor Q νsₐ) where

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
      module _ (𝑆-te! : InitialCtxTypingInstance Γ₀ se) where

        open Σ 𝑆-te! renaming
          ( fst to 𝑆-te
          ; snd to Ω₁
          )

        open CtxTypingInstance 𝑆-te renaming
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
            Proof = α₂ ⇃[ π ◆ ⟨ splitting factor:f ⟩⁻¹ ]⇂      ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α₂} {f = π} {⟨ splitting factor:f ⟩⁻¹}) ⟩-≡
                  -- α₂ ⇃[ π ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂  ⟨ cong _⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ lem-5b ⟩-≡
                  α₂ ⇃[ π ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂  ⟨ cong _⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ ? ⟩-≡
                  (β₂ ⇒ γ₂) ⇃[ π ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ ⟨ functoriality-◆-⇃[]⇂ {τ = β₂ ⇒ γ₂} {f = π} {⟨ splitting factor:f ⟩⁻¹} ⟩-≡
                  (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂                              ∎-≡

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

          -- postulate lem-6 : Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ ≡ Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
          {-
          lem-6 = Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ₂} {f = ι₀} {σ₂₃} ⟩-≡
                  Γ₂ ⇃[ ι₀ ◆ σ₂₃ ]⇂ᶜ       ⟨ Γ₂ ⇃[≀ lem-0 ≀]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ∎-≡
          -}

