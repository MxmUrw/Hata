
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.FreeVarsCarryStrict where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free

-- data
-- open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.Sum.Definition

-- terms / substitutions
-- open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Data.Substitution.Variant.Base.Definition

-- categories
-- open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition

-- limits
-- open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer

open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Proofs
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2
open import Verification.Core.Data.Language.HindleyMilner.Helpers

open import Verification.Core.Set.Decidable
open import Verification.Core.Order.Preorder

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition

open import Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity

{-# DISPLAY isCoequalizer.π₌ _ = π₌ #-}
{-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
{-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = f ◆ g #-}
{-# DISPLAY 内id-⧜𝐒𝐮𝐛𝐬𝐭 = id #-}

instance
  hasSplitEpiMonoFactorization:ℒHMTypes : hasSplitEpiMonoFactorization ℒHMTypes
  hasSplitEpiMonoFactorization:ℒHMTypes = {!!}


--------------------------------------
-- coproduct replacement
-- module _ {𝒞' : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞'}} where
--   private
--     macro 𝒞 = #structureOn ⟨ 𝒞' ⟩
--     instance
--       _ : isSetoid 𝒞
--       _ = isSetoid:byCategory

--   -- unit-l-⊔ : ∀{a : 𝒞} -> ⊥ ⊔ a ∼ a
--   -- unit-l-⊔ = {!!}

--   -- unit-r-⊔ : ∀{a : 𝒞} -> a ⊔ ⊥ ∼ a
--   -- unit-r-⊔ = {!!}

--   postulate
--     assoc-l-⊔ : ∀{a b c : 𝒞} -> (a ⊔ b) ⊔ c ∼ a ⊔ (b ⊔ c)


assoc-l-⊔-ℒHMTypes : ∀{a b c : ℒHMTypes} -> (a ⊔ b) ⊔ c ≅ a ⊔ (b ⊔ c)
assoc-l-⊔-ℒHMTypes = {!!}


record CtxTypingInstance {μs k} {Q : ℒHMQuant k} (Γ : ℒHMCtxFor Q μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _/_⊩_,_,_,_
  field metas : ℒHMTypes
  field typeMetas : ℒHMTypes
  field ctx : ℒHMCtxFor Q (metas) --  ⊔ typeMetas)
  field typ : ℒHMType (⟨ metas ⊔ typeMetas ⟩)
  field isInstance : Γ <Γ ctx
  -- field hiddenEpiSub : μs ⟶ metas
  -- field hiddenEpiSubProof : hiddenEpiSub ◆ ι₀ ∼ (isInstance .fst)
  field hasType : isTypedℒHM (metas ⊔ typeMetas ⊩ (Q , ctx ⇃[ ι₀ ]⇂ᶜ) ⊢ typ) te

open CtxTypingInstance public

-- record CtxTypingInstance {μs k} {Q : ℒHMQuant k} (Γ : ℒHMCtxFor Q μs) (te : UntypedℒHM k) : 𝒰₀ where
--   constructor _⊩_,_,_,_
--   field metas : ℒHMTypes
--   field ctx : ℒHMCtxFor Q (metas) --  ⊔ typeMetas)
--   field typ : ℒHMType (⟨ metas ⟩)
--   field isInstance : Γ <Γ ctx
--   -- field hiddenEpiSub : μs ⟶ metas
--   -- field hiddenEpiSubProof : hiddenEpiSub ◆ ι₀ ∼ (isInstance .fst)
--   field hasType : isTypedℒHM (metas ⊩ (Q , ctx) ⊢ typ) te

-- open CtxTypingInstance public


module _ {μs k} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μs} {te : UntypedℒHM k}  where
  record _<TI_ (𝑇 : CtxTypingInstance Γ te) (𝑆 : CtxTypingInstance Γ te) : 𝒰₀ where
    field tiSubₐ : metas 𝑇 ⟶ metas 𝑆
    field tiSubₓ : typeMetas 𝑇 ⟶ metas 𝑆 ⊔ typeMetas 𝑆
    field typProof : typ 𝑇 ⇃[ ⦗ tiSubₐ ◆ ι₀ , tiSubₓ ⦘ ]⇂ ≡ typ 𝑆
    field subProof : isInstance 𝑇 .fst ◆ tiSubₐ ∼ isInstance 𝑆 .fst

    -- field tiSub : metas 𝑇 ⊔ typeMetas 𝑇 ⟶ metas 𝑆 ⊔ typeMetas 𝑆

    ctxProofTI : ctx 𝑇 ⇃[ tiSubₐ ]⇂ᶜ ≡ ctx 𝑆
    ctxProofTI = {!!}

  open _<TI_ public


InitialCtxTypingInstance : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtxFor Q μs) (te : UntypedℒHM k) -> 𝒰₀
InitialCtxTypingInstance Γ te = ∑ λ (𝑇 : CtxTypingInstance Γ te) -> ∀(𝑆 : CtxTypingInstance Γ te) -> 𝑇 <TI 𝑆

TypingDecision : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtxFor Q μs) (te : UntypedℒHM k) -> 𝒰₀
TypingDecision Γ te = (CtxTypingInstance Γ te -> ⊥-𝒰 {ℓ₀}) + (InitialCtxTypingInstance Γ te)




γ : ∀{μs k} {Q : ℒHMQuant k} -> (Γ : ℒHMCtxFor Q μs) -> (te : UntypedℒHM k)
  -> (CtxTypingInstance Γ te -> ⊥-𝒰 {ℓ₀})
    +
     (InitialCtxTypingInstance Γ te)
γ {μs} {k} {Q} Γ (var k∍i) = {!!}
{-
  let vα = lookup-Listᴰ Q k∍i
      α = lookup-Listᴰ² Γ k∍i
      σᵤ₀ : μs ⟶ μs ⊔ vα
      σᵤ₀ = ι₀

      α₀ = α ⇃[ id ]⇂

      Γ₀ = Γ ⇃[ ι₀ ]⇂ᶜ

      Γ<Γ₀ : Γ <Γ Γ₀
      Γ<Γ₀ = record { fst = σᵤ₀ ; snd = refl-≡ }

      lem-1 : lookup-Listᴰ² (Γ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ι₁ ⦘ ]⇂ ≡ lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂
      lem-1 = trans-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i ι₀ ι₁) (lookup-Listᴰ² Γ k∍i ⇃[≀ §-ℒHMTypes.prop-1 ⁻¹ ≀]⇂)

  in right ((μs / vα ⊩ Γ , α₀ , reflexive , var k∍i ι₁ lem-1)

           -- now we have to prove that this is the "initial" such typing instance
           , λ {(μs₁ / να₁ ⊩ Γ₁ , α₁ , Γ<Γ₁ , var {Γ = Γ₁'} _ ρ Γp) →

               -- given another instance, which has to use `var` to prove the typing

                let σᵤ₁ : μs ⟶ μs₁
                    σᵤ₁ = Γ<Γ₁ .fst


                    σᵤ₁-ty : lookup-Listᴰ Q k∍i ⟶ μs₁ ⊔ να₁
                    σᵤ₁-ty = ρ

                    lem-4 : Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
                    lem-4 = Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                            Γ ⇃[ σᵤ₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ⟨ cong _⇃[ ι₀ ]⇂ᶜ (Γ<Γ₁ .snd) ⟩-≡
                            Γ₁ ⇃[ ι₀ ]⇂ᶜ           ∎-≡


                    lem-5 : lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ ≡ α₁
                    lem-5 = lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

                            ⟨ cong _⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ (functoriality-id-⇃[]⇂ {τ = lookup-Listᴰ² Γ k∍i}) ⟩-≡
                            lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

                            ⟨ sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i (σᵤ₁ ◆ ι₀) (ρ)) ⟩-≡

                            lookup-Listᴰ² (Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

                            ⟨ cong (λ ξ -> lookup-Listᴰ² ξ k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂) lem-4 ⟩-≡

                            lookup-Listᴰ² (Γ₁ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

                            ⟨ Γp ⟩-≡

                            α₁

                            ∎-≡

                in record { tiSubₐ = σᵤ₁ ; tiSubₓ = ρ ; typProof = lem-5 ; subProof = unit-l-◆ }

               })
-}
γ {μs = νs} {Q = Q} Γ (slet te se) = {!!}
{-
  case (γ Γ te) of
  {!!}
  continue₀ where

  continue₀ : InitialCtxTypingInstance Γ te -> TypingDecision Γ (slet te se)
  continue₀ ((νs₀ₐ / νs₀ₓ ⊩ Γ₀ , αᵇ₀ , Γ<Γ₀ , Γ₀⊢αᵇ₀), Ω₀) = result
    where

      -- once we have typechecked te, we know that νs₀ₓ are the
      -- variables over which the type αᵇ₀ is quantified
      -- thus the context in which we typecheck `se` is the following
      α₀Γ₀ : ℒHMCtxFor (νs₀ₓ ∷' Q) νs₀ₐ
      α₀Γ₀ = αᵇ₀ ∷ Γ₀

      σᵃᵤ₀ = fst Γ<Γ₀

      result = case (γ α₀Γ₀ se) of
        {!!}
        continue₁ where

        continue₁ : InitialCtxTypingInstance (α₀Γ₀) se -> TypingDecision Γ (slet te se)
        continue₁ ((νs₁ₐ / νs₁ₓ ⊩ (α₁ ∷ Γ₁) , βᵇ₁ , α₀Γ₀<α₁Γ₁ , α₁Γ₁⊢βᵇ₁), Ω₁) = right (𝑇 , isInitial:𝑇)
          where
            Γ₀<Γ₁ : Γ₀ <Γ Γ₁
            Γ₀<Γ₁ = tail-SomeℒHMCtx α₀Γ₀<α₁Γ₁

            σᵃ₀₁ = fst Γ₀<Γ₁

            α₁' : ℒHMType ⟨ νs₁ₐ ⊔ νs₁ₓ ⊔ νs₀ₓ ⟩
            α₁' = (α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂)

            lem-1a : αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ id ]⇂ ≡ α₁
            lem-1a = λ i -> split-Listᴰ² (α₀Γ₀<α₁Γ₁ .snd i) .fst

            lem-1b : Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ≡ Γ₁
            lem-1b = λ i -> split-Listᴰ² (α₀Γ₀<α₁Γ₁ .snd i) .snd

            Γ₁⊢α₁' : isTypedℒHM (νs₁ₐ ⊔ νs₁ₓ ⊔ νs₀ₓ ⊩ (_ , Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) ⊢ α₁') te
            Γ₁⊢α₁' = Γ₀⊢αᵇ₀
                      >> isTypedℒHM ((νs₀ₐ ⊔ νs₀ₓ) ⊩ Q , (Γ₀ ⇃[ ι₀ ]⇂ᶜ) ⊢ αᵇ₀) te <<
                      ⟪ §-isTypedℒHM.prop-4 σᵃ₀₁ id ⟫
                      >> isTypedℒHM (_ ⊩ Q , (Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ id ]⇂) te <<

                      ⟪ transp-isTypedℒHM (cong _⇃[ ι₀ ]⇂ᶜ lem-1b) lem-1a ⟫

                      >> isTypedℒHM (_ ⊩ Q , (Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₁ ) te <<

                      ⟪ §-isTypedℒHM.prop-4 ι₀ id ⟫

                      >> isTypedℒHM (_ ⊩ Q , (Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ) te <<

                      ⟪ transp-isTypedℒHM (functoriality-◆-⇃[]⇂-CtxFor) refl-≡ ⟫

                      >> isTypedℒHM (_ ⊩ Q , (Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) ⊢ α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ) te <<


            lem-2 : Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ refl-≅ ⟩ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
            lem-2 = trans-Path (functoriality-id-⇃[]⇂-CtxFor) (sym-Path functoriality-◆-⇃[]⇂-CtxFor)

            isAb : isAbstr νs₀ₓ (Γ₁ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ) (Γ₁ ⇃[ ι₀ ]⇂ᶜ) α₁' (α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂)
            isAb = record { metasProof = refl-≅ ; ctxProof = lem-2 ; typeProof = functoriality-id-⇃[]⇂ }


            𝑇 : CtxTypingInstance Γ (slet te se)
            𝑇 = νs₁ₐ / νs₁ₓ ⊩ Γ₁ , βᵇ₁ , Γ<Γ₀ ⟡ Γ₀<Γ₁ , (slet isAb Γ₁⊢α₁' α₁Γ₁⊢βᵇ₁)

            isInitial:𝑇 : ∀(𝑆 : CtxTypingInstance Γ (slet te se)) -> 𝑇 <TI 𝑆
            isInitial:𝑇 (νs₃ₐ / νs₃ₓ ⊩ Γ₃ , β₃ , Γ<Γ₃ , slet {μs = νs₂} {κs = νs₃ₓ₊} {Γ = Γ₂} {α = α₂} {α' = α₃}  isAb₂ Γ₂⊢α₂ α₃Γ₃⊢β₃) =
              record { tiSubₐ = σᵃ₁₃ ; tiSubₓ = σˣ₁₃ ; typProof = lem-30 ; subProof = lem-40 }
              where
                σ₂₃₊ : νs₂ ≅ νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊
                σ₂₃₊ = metasProof isAb₂

                -- lem-10 : isTypedℒHM (νs₃ₐ ⊔ νs₃ₓ ⊔ νs₃ₓ₊ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₃) te
                -- lem-10 = {!!}

                あ : ((νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊) ≅ (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))
                あ = let x = assoc-l-⊔-ℒHMTypes {a = νs₃ₐ} {b = νs₃ₓ} {c = νs₃ₓ₊} in x

                α₃' : ℒHMType ⟨(νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊))⟩
                α₃' = α₃ ⇃[ ⟨ あ ⟩ ]⇂

                lem-11 : isTypedℒHM (νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₃') te
                lem-11 = Γ₂⊢α₂
                         >> isTypedℒHMᵈ (νs₂ ⊩ Q , Γ₂ ⊢ α₂) te <<
                         ⟪ §-isTypedℒHM.prop-2 ⟨ σ₂₃₊ ⟩ ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂ᶜ ⊢ α₂ ⇃[ ⟨ σ₂₃₊ ⟩ ]⇂) te <<
                         ⟪ transp-isTypedℒHM (trans-Path (ctxProof isAb₂) functoriality-◆-⇃[]⇂-CtxFor) (typeProof isAb₂) ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⊢ α₃) te <<
                         ⟪ §-isTypedℒHM.prop-2 ⟨ あ ⟩ ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₃ ⇃[ ι₀ ◆ ι₀ ]⇂ᶜ ⇃[ ⟨ あ ⟩ ]⇂ᶜ ⊢ α₃ ⇃[ ⟨ あ ⟩ ]⇂) te <<
                         ⟪ transp-isTypedℒHM (trans-Path (functoriality-◆-⇃[]⇂-CtxFor) (Γ₃ ⇃[≀ {!!} ≀]⇂ᶜ)) refl-≡ ⟫
                         >> isTypedℒHMᵈ (_ ⊩ Q , Γ₃ ⇃[ ι₀ ]⇂ᶜ ⊢ α₃') te <<

                Ω₀R = Ω₀ ((νs₃ₐ) / (νs₃ₓ ⊔ νs₃ₓ₊) ⊩ Γ₃ , α₃' , Γ<Γ₃ , lem-11)

                σᵃ₀₃ : νs₀ₐ ⟶ νs₃ₐ
                σᵃ₀₃ = tiSubₐ Ω₀R

                σˣ₀₃ : νs₀ₓ ⟶ νs₃ₐ ⊔ (νs₃ₓ ⊔ νs₃ₓ₊)
                σˣ₀₃ = tiSubₓ Ω₀R

                -- σˣ₀₃ : νs₀ₓ ⟶ (νs₃ₐ ⊔ νs₃ₓ) ⊔ νs₃ₓ₊
                -- σˣ₀₃ = σˣ₀₃ᵘ ◆ {!!}

                α₀' = αᵇ₀ ⇃[ σᵃ₀₃ ⇃⊔⇂ id ]⇂

                lem-14 : ⦗ σᵃ₀₃ ◆ ι₀ ◆ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ∼ ⦗ σᵃ₀₃ ◆ ι₀ , σˣ₀₃ ⦘ ◆ ⟨ あ ⟩⁻¹
                lem-14 = {!!}

                lem-15 : α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ≡ α₃
                lem-15 = {!!}

                lem-20 : isTypedℒHM ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₀ₓ ∷ Q) , ((α₀' ∷ Γ₃) ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
                lem-20 = α₃Γ₃⊢β₃
                       >> isTypedℒHMᵈ ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₃ₓ₊ ∷ Q) , (α₃ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                       ⟪ transp-isTypedℒHM ((λ i -> lem-15 (~ i) ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ))) refl-≡ ⟫
                       >> isTypedℒHMᵈ ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₃ₓ₊ ∷ Q) , (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ ι₀ , σˣ₀₃ ◆ ⟨ あ ⟩⁻¹ ⦘ ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<
                       ⟪ {!!} ⟫
                       >> isTypedℒHMᵈ ((νs₃ₐ ⊔ νs₃ₓ) ⊩ (νs₀ₓ ∷ Q) , (α₀' ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ∷ (Γ₃ ⇃[ ι₀ ]⇂ᶜ)) ⊢ β₃) se <<

                α₀Γ₀<α₀'Γ₃ :  α₀Γ₀ <Γ (α₀' ∷ Γ₃)
                α₀Γ₀<α₀'Γ₃ = record { fst = σᵃ₀₃ ; snd = λ i -> α₀' ∷ ctxProofTI Ω₀R i }

                Ω₁R = Ω₁ (νs₃ₐ / νs₃ₓ ⊩ α₀' ∷ Γ₃ , β₃ , α₀Γ₀<α₀'Γ₃ , lem-20)

                σᵃ₁₃ : νs₁ₐ ⟶ νs₃ₐ
                σᵃ₁₃ = tiSubₐ Ω₁R

                σˣ₁₃ : νs₁ₓ ⟶ (νs₃ₐ ⊔ νs₃ₓ)
                σˣ₁₃ = tiSubₓ Ω₁R

                lem-30 : βᵇ₁ ⇃[ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘ ]⇂ ≡ β₃
                lem-30 = let p1 = typProof Ω₁R in p1

                lem-40 : σᵃᵤ₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃ ∼ fst Γ<Γ₃
                lem-40 = σᵃᵤ₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃   ⟨ assoc-l-◆ ⟩-∼
                         σᵃᵤ₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₃) ⟨ refl ◈ subProof Ω₁R ⟩-∼
                         σᵃᵤ₀ ◆ σᵃ₀₃          ⟨ subProof Ω₀R ⟩-∼
                         fst Γ<Γ₃             ∎

-}



-- the case of an application
γ {μs = νsₐ} Γ (app te se) = {!!}
{-
  case (γ Γ te) of
  {!!}
  continue₀ where

  continue₀ : InitialCtxTypingInstance Γ te -> TypingDecision Γ (app te se)
  continue₀ ((νs₀ₐ / νs₀ₓ ⊩ Γ₀ , αᵇ₀ , Γ<Γ₀ , Γ₀⊢αᵇ₀), Ω₀) =
    case (γ _ se) of
    {!!}
    continue₁ where

    continue₁ : InitialCtxTypingInstance Γ₀  se -> TypingDecision Γ (app te se)
    continue₁ ((νs₁ₐ / νs₁ₓ ⊩ Γ₁ , βᵇ₁ , Γ₀<Γ₁ , Γ₁⊢βᵇ₁), Ω₁) = resn res where

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


      res = unify-ℒHMTypes (asArr u) (asArr v)

      resn : (¬ hasCoequalizerCandidate (asArr u , asArr v)) +-𝒰 (hasCoequalizer (asArr u) (asArr v))
            -> (CtxTypingInstance Γ (app te se) -> ⊥-𝒰 {ℓ₀}) + InitialCtxTypingInstance Γ (app te se)
      resn (left _) = {!!}
      resn (right x) = right (𝑇 , {!!}) -- right (𝑇 , isInitial:𝑇)
        where
          -- we now have the coequalizer `π₌`,
          -- but we need to factorize the map ι₀ ◆ π₌
          f : νs₂ₐ ⟶ ⟨ x ⟩
          f = ι₀ ◆ π₌

          factor:f = factorize f

          νs₃ₐ = image factor:f
          νs₃ₓ = rest factor:f

          νs₃ = νs₃ₐ ⊔ νs₃ₓ

          σ₂₃ : νs₂ ⟶ νs₃
          σ₂₃ = π₌ ◆ ⟨ splitting factor:f ⟩⁻¹

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
          postulate lem-5 : α₂ ⇃[ σ₂₃ ]⇂ ≡ (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂
          {-
          lem-5 = α₂ ⇃[ π₌ ◆ ⟨ splitting factor:f ⟩⁻¹ ]⇂      ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α₂} {f = π₌} {⟨ splitting factor:f ⟩⁻¹}) ⟩-≡
                  α₂ ⇃[ π₌ ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂  ⟨ cong _⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ lem-5b ⟩-≡
                  (β₂ ⇒ γ₂) ⇃[ π₌ ]⇂ ⇃[ ⟨ splitting factor:f ⟩⁻¹ ]⇂ ⟨ functoriality-◆-⇃[]⇂ {τ = β₂ ⇒ γ₂} {f = π₌} {⟨ splitting factor:f ⟩⁻¹} ⟩-≡
                  (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂                              ∎-≡

            where
              lem-5a : (asArr α₂) ◆ π₌ ∼ (asArr (β₂ ⇒ γ₂)) ◆ π₌
              lem-5a = equate-π₌

              lem-5a' : ((asArr α₂) ◆-⧜𝐒𝐮𝐛𝐬𝐭 π₌) ∼ ((asArr (β₂ ⇒ γ₂)) ◆-⧜𝐒𝐮𝐛𝐬𝐭 π₌)
              lem-5a' = (abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭 ∙-≣ lem-5a) ∙-≣ (sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭)

              lem-5b : α₂ ⇃[ π₌ ]⇂ ≡ (β₂ ⇒ γ₂) ⇃[ π₌ ]⇂
              lem-5b = let x = lem-5a'
                           y = cong-Str ⟨_⟩ x
                           z = cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 y
                           q = ≡-Str→≡ z
                       in q
          -}

          postulate lem-6 : Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ ≡ Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
          {-
          lem-6 = Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ₂} {f = ι₀} {σ₂₃} ⟩-≡
                  Γ₂ ⇃[ ι₀ ◆ σ₂₃ ]⇂ᶜ       ⟨ Γ₂ ⇃[≀ lem-0 ≀]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ∎-≡
          -}

          -------------
          -- lift the typing of se and te to νs₃

          postulate sp₃ : isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
          {-
          sp₃ = Γ₁⊢βᵇ₁
                >> isTypedℒHM (νs₁ₐ ⊔ νs₁ₓ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ βᵇ₁) se <<
                ⟪ §-isTypedℒHM.prop-3 ι₁ ⟫
                >> isTypedℒHM (νs₁ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₁) se <<
                ⟪ §-isTypedℒHM.prop-3 ι₀ ⟫
                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₁ ⇃[ id ⇃⊔⇂ ι₀ ]⇂) se <<
                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₂) se <<
                ⟪ §-isTypedℒHM.prop-2 {Γ = _ , Γ₂ ⇃[ ι₀ ]⇂ᶜ} {τ = β₂} σ₂₃ ⟫
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ) ⊢ β₂ ⇃[ σ₂₃ ]⇂) se <<
                ⟪ transp-isTypedℒHM lem-6 refl-≡ ⟫
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₂ ⇃[ σ₂₃ ]⇂) se <<
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se <<
          -}

          postulate tp₃ : isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ (β₃ ⇒ γ₃)) te
          {-
          tp₃ = Γ₀⊢αᵇ₀

                >> isTypedℒHM (νs₀ ⊩ (_ , Γ₀ ⇃[ ι₀ ]⇂ᶜ ) ⊢ αᵇ₀ ) te <<

                ⟪ §-isTypedℒHM.prop-4 σᵃ₀₁ ι₀ ⟫

                >> isTypedℒHM (νs₁ ⊩ (_ , Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ) ⊢ αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ ι₀ ]⇂) te <<

                ⟪ transp-isTypedℒHM (cong _⇃[ ι₀ ]⇂ᶜ (Γ₀<Γ₁ .snd)) refl-≡ ⟫

                >> isTypedℒHM (νs₁ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ ) ⊢ α₁ ) te <<

                ⟪ §-isTypedℒHM.prop-3 ι₀ ⟫

                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₁ ⇃[ ι₀ ]⇂ᶜ ) ⊢ α₁ ⇃[ id ⇃⊔⇂ ι₀ ]⇂) te <<
                >> isTypedℒHM (νs₂ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ ) ⊢ α₂) te <<

                ⟪ §-isTypedℒHM.prop-2 σ₂₃ ⟫

                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ) ⊢ α₂ ⇃[ σ₂₃ ]⇂) te <<

                ⟪ transp-isTypedℒHM lem-6 lem-5 ⟫

                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂) te <<
                >> isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃ ⇒ γ₃) te <<
          -}

          -- this shows that we do have the typing instance
          𝑇 : CtxTypingInstance Γ (app te se)
          𝑇 = νs₃ₐ / νs₃ₓ ⊩ Γ₃ , γ₃ , Γ<Γ₃ , (app tp₃ sp₃)

          isInitial:𝑇 : ∀(𝑆 : CtxTypingInstance Γ (app te se)) -> 𝑇 <TI 𝑆
          isInitial:𝑇 (νs₄ₐ / νs₄ₓ ⊩ Ξ , ξ , Γ<Ξ , app {α = ξ₄} {β = ζ₄} Ξ⊢ξ⇒ζ Ξ⊢ξ) =
            record { tiSubₐ = σᵃ₃₄ ; tiSubₓ = σˣ₃₄ ; typProof = lem-32 ; subProof = lem-23 }
            where
              νs₄ : ℒHMTypes
              νs₄ = νs₄ₐ ⊔ νs₄ₓ

              σᵃᵤ₄ : νs ⟶ νs₄ₐ
              σᵃᵤ₄ = fst Γ<Ξ

              ΩR₀ = Ω₀ (νs₄ₐ / νs₄ₓ ⊩ Ξ , ((ξ₄ ⇒ ζ₄)) , Γ<Ξ , Ξ⊢ξ⇒ζ)

              σᵃ₀₄ : νs₀ₐ ⟶ νs₄ₐ
              σᵃ₀₄ = tiSubₐ ΩR₀

              σˣ₀₄ : νs₀ₓ ⟶ νs₄ₐ ⊔ νs₄ₓ
              σˣ₀₄ = tiSubₓ ΩR₀

              Γ₀<Ξ : Γ₀ <Γ Ξ
              Γ₀<Ξ = record { fst = σᵃ₀₄ ; snd = ctxProofTI ΩR₀ }

              ΩR₁ = Ω₁ (νs₄ₐ / νs₄ₓ ⊩ Ξ , ξ₄ , Γ₀<Ξ , Ξ⊢ξ)

              σᵃ₁₄ : νs₁ₐ ⟶ νs₄ₐ
              σᵃ₁₄ = tiSubₐ ΩR₁

              σˣ₁₄ : νs₁ₓ ⟶ νs₄ₐ ⊔ νs₄ₓ
              σˣ₁₄ = tiSubₓ ΩR₁

              -------
              -- we can build a substitution from νs₂ by mapping γ to ζ₄
              --
              σₜ₄ : st ⟶ νs₄
              σₜ₄ = ⧜subst (incl ζ₄)

              σ₂₄ : νs₂ ⟶ νs₄
              σ₂₄ = ⦗ σᵃ₁₄ ◆ ι₀ , ⦗ ⦗ σˣ₀₄ , σˣ₁₄ ⦘ , σₜ₄ ⦘ ⦘ -- ⦗ σ₁₄ , σₜ₄ ⦘
              --
              ------

              -- we know that under this substitution,
              -- u = α₂ and v = β₂ ⇒ γ₂ become both ξ⇒ζ

              postulate lem-11 : u ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
              {-
              lem-11 = αᵇ₀ ⇃[ σᵃ₀₁ ⇃⊔⇂ ι₀ ]⇂ ⇃[ id ⇃⊔⇂ ι₀ ]⇂ ⇃[ σ₂₄ ]⇂     ⟨ {!!} ⟩-≡
                       αᵇ₀ ⇃[ ⦗ σᵃ₀₁ ◆ σᵃ₁₄ ◆ ι₀ , σˣ₀₄ ⦘ ]⇂             ⟨ {!!} ⟩-≡
                       αᵇ₀ ⇃[ ⦗ σᵃ₀₄ ◆ ι₀ , σˣ₀₄ ⦘ ]⇂                    ⟨ typProof ΩR₀ ⟩-≡
                       ξ₄ ⇒ ζ₄                                         ∎-≡
              -}

              -- we show how β₂ and γ₂ evaluate under σ₂₄
              postulate lem-12a : β₂ ⇃[ σ₂₄ ]⇂ ≡ ξ₄
              {-
              lem-12a = βᵇ₁ ⇃[ id ⇃⊔⇂ ι₁ ]⇂ ⇃[ id ⇃⊔⇂ ι₀ ]⇂ ⇃[ σ₂₄ ]⇂   ⟨ {!!} ⟩-≡
                        βᵇ₁ ⇃[ ⦗ σᵃ₁₄ ◆ ι₀ , σˣ₁₄ ⦘ ]⇂                 ⟨ typProof ΩR₁ ⟩-≡
                        ξ₄                                            ∎-≡
              -}

              postulate lem-12b : γ₂ ⇃[ σ₂₄ ]⇂ ≡ ζ₄
              {-
              lem-12b = γᵇₜ ⇃[ ι₁ ◆ ι₁ ]⇂ ⇃[ σ₂₄ ]⇂           ⟨ {!!} ⟩-≡
                        γᵇₜ ⇃[ σₜ₄ ]⇂                         ∎-≡
              -}


{-
              lem-12 : v ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
              lem-12 = λ i -> lem-12a i ⇒ lem-12b i

              -- taken together
              lem-13 : (asArr u) ◆ σ₂₄ ∼ (asArr v) ◆ σ₂₄
              lem-13 = ((sym-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭) ∙-≣ lem-13a) ∙-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭
                where
                  lem-13a : ((asArr u) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ₂₄) ∼ ((asArr v) ◆-⧜𝐒𝐮𝐛𝐬𝐭 σ₂₄)
                  lem-13a = cong-Str ⧜subst (cong-Str incl (≡→≡-Str (trans-Path lem-11 (sym-Path lem-12))))
-}

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

              postulate lem-20 : σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩ ∼ ι₀ ◆ π₌
              {-
              lem-20 = σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩              ⟨ lem-0 ⁻¹ ◈ refl ⟩-∼
                       ι₀ ◆ σ₂₃ ◆ ⟨ ϕ ⟩               ⟨ refl ⟩-∼
                       ι₀ ◆ (π₌ ◆ ⟨ ϕ ⟩⁻¹) ◆ ⟨ ϕ ⟩    ⟨ assoc-l-◆ ∙ (refl ◈ assoc-l-◆) ⟩-∼
                       ι₀ ◆ (π₌ ◆ (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩))  ⟨ refl ◈ (refl ◈ inv-l-◆ (of ϕ)) ⟩-∼
                       ι₀ ◆ (π₌ ◆ id)                ⟨ refl ◈ unit-r-◆ ⟩-∼
                       ι₀ ◆ π₌                       ∎
              -}

              postulate lem-21 : σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε ∼ σᵃ₁₄ ◆ ι₀
              {-
              lem-21 = σᵃ₂₃ ◆ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε      ⟨ lem-20 ◈ refl ⟩-∼
                       ι₀ ◆ π₌ ◆ ε                ⟨ assoc-l-◆ ⟩-∼
                       ι₀ ◆ (π₌ ◆ ε)              ⟨ refl ◈ reduce-π₌ ⟩-∼
                       ι₀ ◆ σ₂₄                   ⟨ reduce-ι₀ ⟩-∼
                       σᵃ₁₄ ◆ ι₀                  ∎
              -}

              postulate lem-22 : σᵃ₂₃ ◆ σᵃ₃₄ ∼ σᵃ₁₄
              {-
              lem-22 = σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε ◆ ϖ₀)    ⟨ assoc-r-◆ ⟩-∼
                       (σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε)) ◆ ϖ₀  ⟨ assoc-r-◆ ◈ refl ⟩-∼
                       ((σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩)) ◆ ε) ◆ ϖ₀ ⟨ assoc-r-◆ ◈ refl ◈ refl ⟩-∼
                       (((σᵃ₂₃ ◆ ι₀) ◆ ⟨ ϕ ⟩) ◆ ε) ◆ ϖ₀ ⟨ lem-21 ◈ refl ⟩-∼
                       σᵃ₁₄ ◆ ι₀ ◆ ϖ₀                  ⟨ assoc-l-◆ ⟩-∼
                       σᵃ₁₄ ◆ (ι₀ ◆ ϖ₀)                ⟨ refl ◈ reduce-ι₀ ⟩-∼
                       σᵃ₁₄ ◆ id                       ⟨ unit-r-◆ ⟩-∼
                       σᵃ₁₄                            ∎
              -}

              postulate lem-22b : σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε) ∼ σᵃ₁₄ ◆ ι₀
              {-
              lem-22b = σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε)     ⟨ assoc-r-◆ ⟩-∼
                        ((σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩)) ◆ ε) ⟨ assoc-r-◆ ◈ refl ⟩-∼
                        (((σᵃ₂₃ ◆ ι₀) ◆ ⟨ ϕ ⟩) ◆ ε) ⟨ lem-21 ⟩-∼
                        σᵃ₁₄ ◆ ι₀                  ∎
              -}

              postulate lem-23 : fst Γ<Γ₃ ◆ σᵃ₃₄ ∼ σᵃᵤ₄
              {-
              lem-23 = (σᵃᵤ₀ ◆ σᵃ₀₁) ◆ σᵃ₂₃ ◆ σᵃ₃₄       ⟨ assoc-l-◆ ⟩-∼
                       (σᵃᵤ₀ ◆ σᵃ₀₁) ◆ (σᵃ₂₃ ◆ σᵃ₃₄)     ⟨ refl ◈ lem-22 ⟩-∼
                       (σᵃᵤ₀ ◆ σᵃ₀₁) ◆ σᵃ₁₄              ⟨ assoc-l-◆ ⟩-∼
                       σᵃᵤ₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₄)              ⟨ refl ◈ subProof ΩR₁ ⟩-∼
                       σᵃᵤ₀ ◆ σᵃ₀₄                       ⟨ subProof ΩR₀  ⟩-∼
                       σᵃᵤ₄                              ∎
              -}

              --------------------------------------
              -- i) the "x" version
              σˣ₃₄ : νs₃ₓ ⟶ νs₄
              σˣ₃₄ = ι₁ ◆ ⟨ ϕ ⟩ ◆ ε

              postulate lem-30 : σᵃ₃₄ ◆ ι₀ ∼ ι₀ ◆ ⟨ ϕ ⟩ ◆ ε
              {-
              lem-30 = cancel-epi {{_}} {{isEpi:epiHom factor:f}} lem-30a
                where
                  lem-30a : σᵃ₂₃ ◆ (σᵃ₃₄ ◆ ι₀) ∼ σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε)
                  lem-30a = σᵃ₂₃ ◆ (σᵃ₃₄ ◆ ι₀)      ⟨ assoc-r-◆ ⟩-∼
                            (σᵃ₂₃ ◆ σᵃ₃₄) ◆ ι₀      ⟨ lem-22 ◈ refl ⟩-∼
                            σᵃ₁₄ ◆ ι₀               ⟨ lem-22b ⁻¹ ⟩-∼
                            σᵃ₂₃ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ ε) ∎
              -}

              lem-31 : σ₂₃ ◆ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ∼ σ₂₄
              lem-31 = σ₂₃ ◆ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘      ⟨ refl ◈ cong-∼ {{isSetoidHom:⦗⦘}} (lem-30 , refl) ⟩-∼
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
                         ⟨ reduce-π₌ ⟩-∼
                       σ₂₄
                         ∎

              lem-32 : γ₃ ⇃[ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ]⇂ ≡ ζ₄
              lem-32 = γ₂ ⇃[ σ₂₃ ]⇂ ⇃[ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = γ₂} {f = σ₂₃} {⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘} ⟩-≡
                       γ₂ ⇃[ σ₂₃ ◆ ⦗ σᵃ₃₄ ◆ ι₀ , σˣ₃₄ ⦘ ]⇂        ⟨ γ₂ ⇃[≀ lem-31 ≀]⇂ ⟩-≡
                       γ₂ ⇃[ σ₂₄ ]⇂                               ⟨ lem-12b ⟩-≡
                       ζ₄                                         ∎-≡
-}

-------------------------------------------------------


-- the case of a lambda
γ {μs} {k} {Q = Q} Γ (lam te) = {!!} -- resn
  where
    -- create a new metavariable
    μs₀ = μs ⊔ st

    αᵘ : ℒHMType ⟨ st ⟩
    αᵘ = var incl

    α₀ : ℒHMType ⟨ μs₀ ⊔ ⊥ ⟩
    α₀ = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂

    -- create the context which contains this new variable
    Γ₀ : ℒHMCtxFor Q μs₀
    Γ₀ = Γ ⇃[ ι₀ ]⇂ᶜ

    σ₀ : μs ⟶ μs ⊔ st
    σ₀ = ι₀

    Γ<Γ₀ : Γ <Γ Γ₀
    Γ<Γ₀ = record { fst = ι₀ ; snd = refl-≡ }

    -- call typechecking recursively on `te`
    res = γ (α₀ ∷ Γ₀) te

    -- computing the initial typing instance
    -- assuming we have one for te
    success : InitialCtxTypingInstance (α₀ ∷ Γ₀) te -> InitialCtxTypingInstance Γ (lam te)
    success ((μs₁ₐ / μs₁ₓ ⊩ (α₁ ∷ Γ₁) , β₁ , α₀Γ₀<α₁Γ₁ , α₁Γ₁⊢β₁) , Ω) = {!!} , {!!} -- 𝑇 , isInitial:𝑇
      where
        σᵃ₀₁ : μs₀ ⟶ μs₁ₐ
        σᵃ₀₁ = α₀Γ₀<α₁Γ₁ .fst

        Γ₀<Γ₁ : Γ₀ <Γ Γ₁
        Γ₀<Γ₁ = tail-SomeℒHMCtx (α₀Γ₀<α₁Γ₁)

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


        -- σᵤ₁ : μs ⟶ μs₁
        -- σᵤ₁ = σ₀ ◆ σ₀₁

        -- Γ<Γ₁ : Γ <Γ Γ₁
        -- Γ<Γ₁ = Γ<Γ₀ ⟡ tail-SomeℒHMCtx α₀Γ₀<α₁Γ₁

        Γ₂ = Γ ⇃[ σᵃᵤ₂ ]⇂ᶜ

        あ : (μs₂ₐ ⊔ μs₂ₓ) ⊔ μs₁ₓ ≅ μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ)
        あ = assoc-l-⊔-ℒHMTypes

        ψ⁻¹ : (μs₁ₐ ⊔ μs₁ₓ) ⟶ μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ)
        ψ⁻¹ = (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩

        α₂ : ℒHMType ⟨ μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ) ⟩
        α₂ = α₁ ⇃[ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ]⇂


        β₂ : ℒHMType ⟨ μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ) ⟩
        β₂ = β₁ ⇃[ ψ⁻¹ ]⇂

        postulate lem-03 : ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ ψ⁻¹)) ∼ σᵃᵤ₂ ◆ ι₀
        {-
        lem-03 = ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ ((⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩)))

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

                 ⟨ refl ◈ {!!} ⟩-∼

                 σᵃᵤ₂ ◆ ι₀

                 ∎
        -}

        postulate lem-04a : Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ψ⁻¹ ]⇂ᶜ ≡ Γ ⇃[ σᵃᵤ₂ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
        {-
        lem-04a = Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ψ⁻¹ ]⇂ᶜ      ⟨ functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ₁} {f = ι₀} {ψ⁻¹} ⟩-≡
                  Γ₁ ⇃[ ι₀ ◆ ψ⁻¹ ]⇂ᶜ           ⟨ cong _⇃[ ι₀ ◆ ψ⁻¹ ]⇂ᶜ (sym-Path (snd Γ₀<Γ₁)) ⟩-≡
                  Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₁ ]⇂ᶜ ⇃[ ι₀ ◆ ψ⁻¹ ]⇂ᶜ   ⟨ functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                  Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₁ ◆ (ι₀ ◆ ψ⁻¹) ]⇂ᶜ   ⟨ functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                  Γ ⇃[ ι₀ ◆ (σᵃ₀₁ ◆ (ι₀ ◆ ψ⁻¹)) ]⇂ᶜ       ⟨ Γ ⇃[≀ lem-03 ≀]⇂ᶜ ⟩-≡
                  Γ ⇃[ σᵃᵤ₂ ◆ ι₀ ]⇂ᶜ           ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                  Γ ⇃[ σᵃᵤ₂ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ      ∎-≡
        -}

        postulate lem-04b : α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ψ⁻¹ ]⇂ ≡ α₂
        {-
        lem-04b = α₁ ⇃[ ι₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ψ⁻¹ ]⇂

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
        -}


        postulate lem-05 : isTypedℒHM (μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ) ⊩ (_ , Γ₂ ⇃[ ι₀ ]⇂ᶜ) ⊢ α₂ ⇒ β₂) (lam te)
        {-
        lem-05 = lam α₁Γ₁⊢β₁
                 ⟪ §-isTypedℒHM.prop-2 ψ⁻¹ ⟫
                 >> isTypedℒHM ((μs₂ₐ ⊔ (μs₂ₓ ⊔ μs₁ₓ)) ⊩ (Q) , (Γ₁ ⇃[ ι₀ ]⇂ᶜ ⇃[ ψ⁻¹ ]⇂ᶜ) ⊢ _ ⇒ β₂) (lam te) <<

                 ⟪ transp-isTypedℒHM lem-04a (λ i -> lem-04b i ⇒ β₂) ⟫
        -}


        Γ<Γ₂ : Γ <Γ Γ₂
        Γ<Γ₂ = record { fst = σᵃᵤ₂ ; snd = refl-≡ }

        𝑇 : CtxTypingInstance Γ (lam te)
        𝑇 = μs₂ₐ / (μs₂ₓ ⊔ μs₁ₓ) ⊩ Γ₂ , α₂ ⇒ β₂ , Γ<Γ₂ , (lem-05)


        isInitial:𝑇 : (𝑆 : CtxTypingInstance Γ (lam te)) -> 𝑇 <TI 𝑆
        isInitial:𝑇 (μs₃ₐ / μs₃ₓ ⊩ Γ₃ , .(_ ⇒ _) , Γ<Γ₃ , lam {α = α₃} {β = β₃} Γ₃α₃⊢β₃) =
          record { tiSubₐ = σᵃ₂₃ ; tiSubₓ = σˣ₂₃ ; typProof = lem-50 ; subProof = lem-20 }

          where
            σᵃᵤ₃ : μs ⟶ μs₃ₐ
            σᵃᵤ₃ = Γ<Γ₃ .fst

            β₃' : ℒHMType ⟨(μs₃ₐ ⊔ μs₃ₓ ⊔ ⊥)⟩
            β₃' = β₃ ⇃[ ι₀ ]⇂

            Γ₃' : ℒHMCtxFor _ (μs₃ₐ ⊔ μs₃ₓ)
            Γ₃' = Γ₃ ⇃[ ι₀ ]⇂ᶜ

            lem-9 : isTypedℒHM (μs₃ₐ ⊔ μs₃ₓ ⊔ ⊥ ⊩ (_ , (α₃ ∷ Γ₃') ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃') te
            lem-9 = Γ₃α₃⊢β₃
                    ⟪ §-isTypedℒHM.prop-2 ι₀ ⟫

            α₃' : ℒHMType ⟨ μs₃ₐ ⊔ μs₃ₓ ⟩
            α₃' = α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

            σα₃ : st ⟶ μs₃ₐ ⊔ μs₃ₓ
            σα₃ = ⧜subst (incl α₃')

            σᵃ₀₃' : μs₀ ⟶ μs₃ₐ ⊔ μs₃ₓ
            σᵃ₀₃' = ⦗ σᵃᵤ₃ ◆ ι₀ , σα₃ ⦘

            postulate lem-10a : α₀ ⇃[ σᵃ₀₃' ⇃⊔⇂ id ]⇂ ≡ α₃
            {-
            lem-10a = αᵘ ⇃[ ι₁ ◆ ι₀ ]⇂ ⇃[ σᵃ₀₃' ⇃⊔⇂ id ]⇂     ⟨ functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = ι₁ ◆ ι₀} {σᵃ₀₃' ⇃⊔⇂ id} ⟩-≡
                      αᵘ ⇃[ ι₁ ◆ ι₀ ◆ (σᵃ₀₃' ⇃⊔⇂ id) ]⇂       ⟨ αᵘ ⇃[≀ lem-10ai ≀]⇂ ⟩-≡
                      αᵘ ⇃[ σα₃ ◆ ι₀ ]⇂                       ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = αᵘ} {f = σα₃} {ι₀}) ⟩-≡
                      αᵘ ⇃[ σα₃ ]⇂ ⇃[ ι₀ ]⇂                   ⟨ refl-≡ ⟩-≡
                      α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ ι₀ ]⇂       ⟨ functoriality-◆-⇃[]⇂ {τ = α₃} {f = ⦗ id , elim-⊥ ⦘} {ι₀} ⟩-≡
                      α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ◆ ι₀ ]⇂           ⟨ α₃ ⇃[≀ §-ϖ.prop-1  ≀]⇂ ⟩-≡
                      α₃ ⇃[ id ]⇂                             ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                      α₃                                      ∎-≡
              where
                postulate lem-10ai : ι₁ ◆ ι₀ ◆ (σᵃ₀₃' ⇃⊔⇂ id) ∼ σα₃ ◆ ι₀
                {-
                lem-10ai = ι₁ ◆ ι₀ ◆ (σᵃ₀₃' ⇃⊔⇂ id)     ⟨ assoc-l-◆ ⟩-∼
                           ι₁ ◆ (ι₀ ◆ (σᵃ₀₃' ⇃⊔⇂ id))   ⟨ refl ◈ reduce-ι₀ ⟩-∼
                           ι₁ ◆ (σᵃ₀₃' ◆ ι₀)            ⟨ assoc-r-◆ ⟩-∼
                           (ι₁ ◆ σᵃ₀₃') ◆ ι₀            ⟨ reduce-ι₁ ◈ refl ⟩-∼
                           (σα₃) ◆ ι₀                   ∎
                -}
            -}

            postulate lem-10b : Γ₀ ⇃[ σᵃ₀₃' ]⇂ᶜ ≡ Γ₃'
            {-
            lem-10b = Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σᵃ₀₃' ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                      Γ ⇃[ ι₀ ◆ σᵃ₀₃' ]⇂ᶜ       ⟨ Γ ⇃[≀ reduce-ι₀ ≀]⇂ᶜ ⟩-≡
                      Γ ⇃[ σᵃᵤ₃ ◆ ι₀ ]⇂ᶜ        ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                      Γ ⇃[ σᵃᵤ₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ   ⟨ cong _⇃[ ι₀ ]⇂ᶜ (snd Γ<Γ₃) ⟩-≡
                      Γ₃ ⇃[ ι₀ ]⇂ᶜ              ∎-≡
            -}

            α₀Γ₀<α₃Γ₃' : (α₀ ∷ Γ₀) <Γ (α₃ ∷ Γ₃')
            α₀Γ₀<α₃Γ₃' = record { fst = σᵃ₀₃' ; snd = λ i → lem-10a i ∷ lem-10b i }

            ΩR = Ω ((μs₃ₐ ⊔ μs₃ₓ) / ⊥ ⊩ α₃ ∷ Γ₃' , β₃' , α₀Γ₀<α₃Γ₃' , lem-9)

            σᵃ₁₃ : μs₁ₐ ⟶ μs₃ₐ ⊔ μs₃ₓ
            σᵃ₁₃ = tiSubₐ ΩR

            σˣ₁₃ : μs₁ₓ ⟶ (μs₃ₐ ⊔ μs₃ₓ) ⊔ ⊥
            σˣ₁₃ = tiSubₓ ΩR

            σᵃ₂₃ : μs₂ₐ ⟶ μs₃ₐ
            σᵃ₂₃ = ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ ◆ ϖ₀
            -- σ₂₃ ◆ ϖ₀

            σˣ₂₃ : (μs₂ₓ ⊔ μs₁ₓ) ⟶ μs₃ₐ ⊔ μs₃ₓ
            σˣ₂₃ = ⦗ ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘

            postulate lem-15 : σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩) ∼ ι₀ ◆ σᵃ₀₁
            {-
            lem-15 = σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩)             ⟨ assoc-r-◆ ⟩-∼
                     (σᵃᵤ₂ ◆ ι₀) ◆ ⟨ ϕ ⟩             ⟨ lem-0 ◈ refl ⟩-∼
                     ι₀ ◆ σᵃ₀₁ ◆ ⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩     ⟨ assoc-l-◆ ⟩-∼
                     ι₀ ◆ σᵃ₀₁ ◆ (⟨ ϕ ⟩⁻¹ ◆ ⟨ ϕ ⟩)   ⟨ refl ◈ inv-l-◆ (of ϕ) ⟩-∼
                     ι₀ ◆ σᵃ₀₁ ◆ id                 ⟨ unit-r-◆ ⟩-∼
                     ι₀ ◆ σᵃ₀₁                      ∎
            -}

            postulate lem-16 : σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃) ∼ σᵃᵤ₃ ◆ ι₀
            {-
            lem-16 = σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃)     ⟨ assoc-r-◆ ⟩-∼
                     σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩) ◆ σᵃ₁₃     ⟨ lem-15 ◈ refl ⟩-∼
                     ι₀ ◆ σᵃ₀₁ ◆ σᵃ₁₃               ⟨ assoc-l-◆ ⟩-∼
                     ι₀ ◆ (σᵃ₀₁ ◆ σᵃ₁₃)             ⟨ refl ◈ subProof ΩR ⟩-∼
                     ι₀ ◆ (σᵃ₀₃')                   ⟨ reduce-ι₀ ⟩-∼
                     (σᵃᵤ₃ ◆ ι₀)                    ∎
            -}

            postulate lem-20 : σᵃᵤ₂ ◆ σᵃ₂₃ ∼ σᵃᵤ₃
            {-
            lem-20 = σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ ◆ ϖ₀)  ⟨ assoc-r-◆ ⟩-∼
                     σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃) ◆ ϖ₀  ⟨ lem-16 ◈ refl ⟩-∼
                     σᵃᵤ₃ ◆ ι₀ ◆ ϖ₀                   ⟨ assoc-l-◆ ⟩-∼
                     σᵃᵤ₃ ◆ (ι₀ ◆ ϖ₀)                 ⟨ refl ◈ reduce-ι₀ ⟩-∼
                     σᵃᵤ₃ ◆ id                        ⟨ unit-r-◆ ⟩-∼
                     σᵃᵤ₃                             ∎
            -}

            postulate lem-30 : σᵃ₂₃ ◆ ι₀ ∼ ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃
            {-
            lem-30 = cancel-epi {{_}} {{isEpi:epiHom factor:f}} lem-30a
              where
                lem-30a : σᵃᵤ₂ ◆ (σᵃ₂₃ ◆ ι₀) ∼ σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃)
                lem-30a = σᵃᵤ₂ ◆ (σᵃ₂₃ ◆ ι₀)           ⟨ assoc-r-◆ ⟩-∼
                          (σᵃᵤ₂ ◆ σᵃ₂₃) ◆ ι₀           ⟨ lem-20 ◈ refl ⟩-∼
                          σᵃᵤ₃ ◆ ι₀                    ⟨ lem-16 ⁻¹ ⟩-∼
                          σᵃᵤ₂ ◆ (ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃)   ∎
            -}

            -------------------------------------------------
            -- these lemmas are needed for the α₂ ⇃[ "σ₂₃" ]⇂ ≡ α₃ proof
            postulate lem-31 : ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ∼ ⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘
            {-
            lem-31 = ⦗ σᵃ₂₃ ◆ ι₀ , ⦗ ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘ ⦘

                     ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (lem-30 , refl) ⟩-∼

                     ⦗ ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , ⦗ ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘ ⦘

                     ⟨ {!!} ⟩-∼

                     ⟨ あ ⟩⁻¹ ◆ ⦗ ⦗ ι₀ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , ι₁ ◆ ⟨ ϕ ⟩ ◆ σᵃ₁₃ ⦘ , σˣ₁₃ ◆ ϖ₀ ⦘

                     ⟨ refl ◈ ⦗≀ ⦗≀ assoc-l-◆ , assoc-l-◆ ≀⦘ , refl ≀⦘ ⟩-∼

                     ⟨ あ ⟩⁻¹ ◆ ⦗ ⦗ ι₀ ◆ (⟨ ϕ ⟩ ◆ σᵃ₁₃) , ι₁ ◆ (⟨ ϕ ⟩ ◆ σᵃ₁₃) ⦘ , σˣ₁₃ ◆ ϖ₀ ⦘

                     ⟨ refl ◈ ⦗≀ expand-ι₀,ι₁ ⁻¹ , refl ≀⦘ ⟩-∼

                     ⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘

                     ∎
            -}

            postulate lem-32 : ψ⁻¹ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘) ∼ ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘
            {-
            lem-32 = (⟨ ϕ ⟩⁻¹ ⇃⊔⇂ id) ◆ ⟨ あ ⟩ ◆ (⟨ あ ⟩⁻¹ ◆ _)

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
            -}

            postulate lem-33 : ι₀ ◆ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘) ∼ σᵃ₁₃
            {-
            lem-33 = ι₀ ◆ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ _

                     ⟨ reduce-ι₀ ◈ refl ⟩-∼

                     ι₀ ◆ ψ⁻¹ ◆ _

                     ⟨ assoc-l-◆ ⟩-∼

                     ι₀ ◆ (ψ⁻¹ ◆ _)

                     ⟨ refl ◈ lem-32 ⟩-∼

                     ι₀ ◆ ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘

                     ⟨ reduce-ι₀ ⟩-∼

                     σᵃ₁₃

                     ∎
            -}


            postulate lem-34 : ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘) ∼ (σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘
            {-
            lem-34 = §-ϖ.prop-2 lem-34a
              where
                lem-34a : ι₀ ◆ (⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘)) ∼ ι₀ ◆ ((σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘)
                lem-34a = ι₀ ◆ (⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘))

                          ⟨ refl ◈ (refl ◈ lem-31 ) ⟩-∼

                          ι₀ ◆ (⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘))

                          ⟨ assoc-r-◆ ⟩-∼

                          (ι₀ ◆ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘) ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘)

                          ⟨ lem-33 ⟩-∼

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
            -}

            postulate lem-35 : α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂ ≡ α₀ ⇃[ σᵃ₀₃' ⇃⊔⇂ id ]⇂
            {-
            lem-35 = α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂                         ⟨ sym-Path (cong _⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂ (λ i -> split-Listᴰ² (α₀Γ₀<α₁Γ₁ .snd i) .fst)) ⟩-≡
                     α₀ ⇃[ (σᵃ₀₁ ⇃⊔⇂ id) ]⇂ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂     ⟨ functoriality-◆-⇃[]⇂ {τ = α₀} {f = (σᵃ₀₁ ⇃⊔⇂ id)} {(σᵃ₁₃ ⇃⊔⇂ id)} ⟩-≡
                     α₀ ⇃[ (σᵃ₀₁ ⇃⊔⇂ id) ◆ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂         ⟨ α₀ ⇃[≀ functoriality-◆-⊔ ⁻¹ ≀]⇂ ⟩-≡
                     α₀ ⇃[ ((σᵃ₀₁ ◆ σᵃ₁₃) ⇃⊔⇂ (id ◆ id)) ]⇂             ⟨ α₀ ⇃[≀ subProof ΩR ≀⇃⊔⇂≀ unit-2-◆ ≀]⇂ ⟩-≡
                     α₀ ⇃[ (σᵃ₀₃' ⇃⊔⇂ id) ]⇂                        ∎-≡
            -}

            postulate lem-40 : α₂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂ ≡ α₃'
            {-
            lem-40 = α₁ ⇃[ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂

                     ⟨ functoriality-◆-⇃[]⇂ {τ = α₁} {f = ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘} {⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘} ⟩-≡

                     α₁ ⇃[ ⦗ ι₀ ◆ ψ⁻¹ , elim-⊥ ⦘ ◆ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂

                     ⟨ α₁ ⇃[≀ lem-34 ≀]⇂ ⟩-≡

                     α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ]⇂

                     ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α₁} {f = (σᵃ₁₃ ⇃⊔⇂ id)} {⦗ id , elim-⊥ ⦘}) ⟩-≡

                     α₁ ⇃[ (σᵃ₁₃ ⇃⊔⇂ id) ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

                     ⟨ cong _⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ lem-35 ⟩-≡

                     α₀ ⇃[ (σᵃ₀₃' ⇃⊔⇂ id) ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

                     ⟨ cong _⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ (λ i -> split-Listᴰ² (α₀Γ₀<α₃Γ₃' .snd i) .fst) ⟩-≡

                     α₃ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂

                     ⟨ refl-≡ ⟩-≡

                     α₃'

                     ∎-≡
            -}

            -------------------------------------------------------
            -- now the lemmas for β₂ ⇃[ "σ₂₃" ]⇂ ≡ β₃ proof

            postulate lem-41 : β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀ ]⇂ ≡ β₃'
            {-
            lem-41 = β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀ ]⇂

                     ⟨ (functoriality-◆-⇃[]⇂ {τ = β₁} {f = ψ⁻¹} {⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀}) ⟩-≡

                     β₁ ⇃[ ψ⁻¹ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ]⇂

                     ⟨ β₁ ⇃[≀ lem-41a ≀]⇂ ⟩-≡

                     β₁ ⇃[ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘ ]⇂

                     ⟨ typProof ΩR ⟩-≡

                     β₃'

                     ∎-≡

              where
                postulate lem-41a : ψ⁻¹ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ∼ ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘
                {-
                lem-41a = ψ⁻¹ ◆ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀)

                      ⟨ assoc-r-◆ ⟩-∼

                      (ψ⁻¹ ◆ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘) ◆ ι₀

                      ⟨ (refl ◈ lem-31) ◈ refl ⟩-∼

                      ψ⁻¹ ◆ (⟨ あ ⟩⁻¹ ◆ ⦗ ⟨ ϕ ⟩ ◆ σᵃ₁₃ , σˣ₁₃ ◆ ϖ₀ ⦘) ◆ ι₀

                      ⟨ lem-32 ◈ refl ⟩-∼

                      ⦗ σᵃ₁₃ , (σˣ₁₃ ◆ ϖ₀) ⦘ ◆ ι₀

                      ⟨ append-⦗⦘ ⟩-∼

                      ⦗ σᵃ₁₃ ◆ ι₀ , (σˣ₁₃ ◆ ϖ₀) ◆ ι₀ ⦘

                      ⟨ ⦗≀ refl , assoc-l-◆ ≀⦘ ⟩-∼

                      ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ◆ (ϖ₀ ◆ ι₀) ⦘

                      ⟨ ⦗≀ refl , ((refl ◈ §-ϖ.prop-1) ∙ unit-r-◆) ≀⦘ ⟩-∼

                      ⦗ σᵃ₁₃ ◆ ι₀ , σˣ₁₃ ⦘

                      ∎
                -}
            -}

            postulate lem-42 : β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂ ≡ β₃
            {-
            lem-42 = β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂

                     ⟨ β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[≀ unit-r-◆ ⁻¹ ∙ (refl ◈ reduce-ι₀ ⁻¹) ∙ assoc-r-◆ ≀]⇂ ⟩-≡

                     β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ◆ ϖ₀ ]⇂

                     ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = β₁ ⇃[ ψ⁻¹ ]⇂} {f = (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀)} {ϖ₀}) ⟩-≡

                     β₁ ⇃[ ψ⁻¹ ]⇂ ⇃[ (⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ◆ ι₀) ]⇂ ⇃[ ϖ₀ ]⇂

                     ⟨ cong _⇃[ ϖ₀ ]⇂ lem-41 ⟩-≡

                     β₃ ⇃[ ι₀ ]⇂ ⇃[ ϖ₀ ]⇂

                     ⟨ functoriality-◆-⇃[]⇂ {τ = β₃} {f = ι₀} {ϖ₀} ⟩-≡

                     β₃ ⇃[ ι₀ ◆ ϖ₀ ]⇂

                     ⟨ β₃ ⇃[≀ reduce-ι₀ ≀]⇂ ⟩-≡

                     β₃ ⇃[ id ]⇂

                     ⟨ functoriality-id-⇃[]⇂ ⟩-≡

                     β₃

                     ∎-≡
            -}


            lem-50 : (α₂ ⇒ β₂) ⇃[ ⦗ σᵃ₂₃ ◆ ι₀ , σˣ₂₃ ⦘ ]⇂ ≡ α₃' ⇒ β₃
            lem-50 = λ i -> lem-40 i ⇒ lem-42 i

{-
    -------------------------------------------------
    -- putting it together

    -- distinguish between failure and not
    resn = case res of
      -- if there was a failure,
      -- we also have to fail
      (λ ¬typing → left
         -- assume we have a typing for lambda
         -- this means that we also have a typing for te
         -- which we know is impossible
         λ {(νs ⊩ Δ , τ , Γ₀<Δ , hastyp)
                → let νs' , Δ' , τ' , hastyp' = §-isTypedℒHM.prop-1 te hastyp
                  in {!!} -- ¬typing (νs' ⊩ Δ' , τ' , {!!} , hastyp')
                  })
      (right ∘ success)
-}


