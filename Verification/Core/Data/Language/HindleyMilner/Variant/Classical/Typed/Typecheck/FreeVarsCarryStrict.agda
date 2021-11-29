
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.FreeVarsCarryStrict where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Monads
-- open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Proofs
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2
open import Verification.Core.Data.Language.HindleyMilner.Helpers

open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Set.Decidable
open import Verification.Core.Order.Preorder

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition

open import Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition

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
γ {μs} {k} {Q} Γ (var k∍i) =
  let vα = lookup-DList Q k∍i
      α = lookup-DDList Γ k∍i
      σᵤ₀ : μs ⟶ μs ⊔ vα
      σᵤ₀ = ι₀

      α₀ = α ⇃[ id ]⇂

      Γ₀ = Γ ⇃[ ι₀ ]⇂ᶜ

      Γ<Γ₀ : Γ <Γ Γ₀
      Γ<Γ₀ = record { fst = σᵤ₀ ; snd = refl-≡ }

      lem-1 : lookup-DDList (Γ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ι₁ ⦘ ]⇂ ≡ lookup-DDList Γ k∍i ⇃[ id ]⇂
      lem-1 = trans-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i ι₀ ι₁) (lookup-DDList Γ k∍i ⇃[≀ §-ℒHMTypes.prop-1 ⁻¹ ≀]⇂)

  in right ((μs / vα ⊩ Γ , α₀ , reflexive , var k∍i ι₁ lem-1)

           -- now we have to prove that this is the "initial" such typing instance
           , λ {(μs₁ / να₁ ⊩ Γ₁ , α₁ , Γ<Γ₁ , var {Γ = Γ₁'} _ ρ Γp) →

               -- given another instance, which has to use `var` to prove the typing

                let σᵤ₁ : μs ⟶ μs₁
                    σᵤ₁ = Γ<Γ₁ .fst


                    σᵤ₁-ty : lookup-DList Q k∍i ⟶ μs₁ ⊔ να₁
                    σᵤ₁-ty = ρ

                    lem-4 : Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
                    lem-4 = Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                            Γ ⇃[ σᵤ₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ⟨ cong _⇃[ ι₀ ]⇂ᶜ (Γ<Γ₁ .snd) ⟩-≡
                            Γ₁ ⇃[ ι₀ ]⇂ᶜ           ∎-≡


                    lem-5 : lookup-DDList Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ ≡ α₁
                    lem-5 = lookup-DDList Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

                            ⟨ cong _⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ (functoriality-id-⇃[]⇂ {τ = lookup-DDList Γ k∍i}) ⟩-≡
                            lookup-DDList Γ k∍i ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

                            ⟨ sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i (σᵤ₁ ◆ ι₀) (ρ)) ⟩-≡

                            lookup-DDList (Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

                            ⟨ cong (λ ξ -> lookup-DDList ξ k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂) lem-4 ⟩-≡

                            lookup-DDList (Γ₁ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

                            ⟨ Γp ⟩-≡

                            α₁

                            ∎-≡

                in record { tiSubₐ = σᵤ₁ ; tiSubₓ = ρ ; typProof = lem-5 ; subProof = unit-l-◆ }

               })

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
            lem-1a = λ i -> split-DDList (α₀Γ₀<α₁Γ₁ .snd i) .fst

            lem-1b : Γ₀ ⇃[ σᵃ₀₁ ]⇂ᶜ ≡ Γ₁
            lem-1b = λ i -> split-DDList (α₀Γ₀<α₁Γ₁ .snd i) .snd

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


{-
  where
    σᵤ₀ : νs ⟶ νs₀
    σᵤ₀ = Γ<Γ₀ .fst

    withAbstr :
              -- (∑ λ νs₁ -> ∑ λ νs₁ₓ -> ∑ λ (Γ₁ : ℒHMCtxFor Q νs₁) -> ∑ λ (τ₁ : ℒHMType ⟨ νs₁ ⊔ νs₁ₓ ⟩)
              -- -> isAbstr _ Γ₀ Γ₁ τ₀ τ₁)
              InitialAbstraction Γ₀ τ₀
              -> (CtxTypingInstance Γ (slet te se) -> ⊥-𝒰 {ℓ₀}) + InitialCtxTypingInstance Γ (slet te se)
    withAbstr ((νs₁ₓ , abstraction νs₁ Γ₁ τ₁ isAb) , 𝐴) = {!!}
      where
        res = γ (τ₁ ∷ Γ₁) se

        σ₀₁ : νs₀ ⟶ νs₁
        σ₀₁ = metasForget isAb

        σᵤ₁ : νs ⟶ νs₁
        σᵤ₁ = σᵤ₀ ◆ σ₀₁

        Γ₀<Γ₁ : somectx Γ₀ ≤ somectx Γ₁
        Γ₀<Γ₁ = record { fst = σ₀₁ ; snd = ctxProof isAb }

        success : InitialCtxTypingInstance (τ₁ ∷ Γ₁) se -> InitialCtxTypingInstance Γ (slet te se)
        success ((νs₂ ⊩ (τ₂ ∷ Γ₂) , α₂ , τ₁Γ₁<τ₂Γ₂ , τ₂Γ₂⊢α₂) , Ω₁) = 𝑇 , {!!}
          where
            σ₁₂ : νs₁ ⟶ νs₂
            σ₁₂ = τ₁Γ₁<τ₂Γ₂ .fst

            Γ₁<Γ₂ = tail-SomeℒHMCtx τ₁Γ₁<τ₂Γ₂

            -- σ₀₁ₓ : νs₀ ⟶ νs₁ ⊔ νs₁ₓ
            -- σ₀₁ₓ = ⟨ metasProof isAb ⟩⁻¹

            -- Γ₁ₓ = Γ₀ ⇃[ σ₀₁ₓ ]⇂ᶜ
            -- τ₁ₓ = τ₀ ⇃[ σ₀₁ₓ ]⇂

            -- Γ₁ₓ⊢τ₁ₓ : isTypedℒHM (νs₁ ⊔ νs₁ₓ ⊩ (_ , Γ₁ₓ) ⊢ τ₁ₓ) te
            -- Γ₁ₓ⊢τ₁ₓ = §-isTypedℒHM.prop-2 σ₀₁ₓ Γ₀⊢τ₀

            isAbstr₀,₁' : isAbstr νs₁ₓ Γ₀ (Γ₁ ⇃[ σ₁₂ ]⇂ᶜ) τ₀ (τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂) --  Γ₁ₓ τ₀ τ₁ₓ
            isAbstr₀,₁' = §-isAbstr.prop-1 σ₁₂ isAb

            isAbstr₀,₂ : isAbstr νs₁ₓ Γ₀ (Γ₂) τ₀ (τ₂) --  Γ₁ₓ τ₀ τ₁ₓ
            isAbstr₀,₂ = transport (λ i -> isAbstr νs₁ₓ Γ₀ (Γ₁₂ i) τ₀ (τ₁₂ i)) isAbstr₀,₁'
              where
                Γ₁₂ : Γ₁ ⇃[ σ₁₂ ]⇂ᶜ ≡ Γ₂
                Γ₁₂ = λ i -> split-DDList (τ₁Γ₁<τ₂Γ₂ .snd i) .snd

                τ₁₂ : τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂ ≡ τ₂
                τ₁₂ = λ i -> split-DDList (τ₁Γ₁<τ₂Γ₂ .snd i) .fst

            Γ₂⊢α₂ : isTypedℒHM (νs₂ ⊩ (_ , Γ₂) ⊢ α₂) (slet te se)
            Γ₂⊢α₂ = slet isAbstr₀,₂ Γ₀⊢τ₀ τ₂Γ₂⊢α₂

            σᵤ₂ : νs ⟶ νs₂
            σᵤ₂ = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂

            Γ<Γ₂ : Γ <Γ Γ₂
            Γ<Γ₂ = Γ<Γ₀ ⟡ Γ₀<Γ₁ ⟡ Γ₁<Γ₂

            𝑇 : CtxTypingInstance Γ (slet te se)
            𝑇 = νs₂ ⊩ Γ₂ , α₂ , Γ<Γ₂ , Γ₂⊢α₂

            isInitial:𝑇 : ∀(𝑆 : CtxTypingInstance Γ (slet te se)) -> 𝑇 <TI 𝑆
            isInitial:𝑇 (νs₄ ⊩ Γ₄ , α₄ , Γ<Γ₄ , slet {μs = νs₃} {κs = νs₄ₓ} {Γ = Γ₃} {Γ₄} {τ₃} {τ₄} isAb₃ Γ₃⊢τ₃ τ₄Γ₄⊢α₄) =
              record { tiSub = σ₂₄ ; typProof = {!!} ; subProof = lem-20 }
              where
                σᵤ₄ = Γ<Γ₄ .fst

                Γ₄<Γ₃ : somectx Γ₄ ≤ somectx Γ₃
                Γ₄<Γ₃ = metasCreate isAb₃
                -- record { fst = {!metasForget isAb₃!} ; snd = {!!} }

                Ω₀R = Ω₀ (νs₃ ⊩ Γ₃ , τ₃ , Γ<Γ₄ ⟡ Γ₄<Γ₃ , Γ₃⊢τ₃)

                σ₀₃ : νs₀ ⟶ νs₃
                σ₀₃ = tiSub Ω₀R

                lem-1 : τ₀ ⇃[ σ₀₃ ]⇂ ≡ τ₃
                lem-1 = typProof Ω₀R

                -- ρ : νs₁ ⟶ νs₄
                -- ρ = {!!}

                ρ : νs₁ ⊔ νs₁ₓ ⟶ νs₄ ⊔ νs₄ₓ
                ρ = {!!}

                ρ⃨ : νs₁ ⟶ νs₄
                ρ⃨ = {!!}

                lem-2 : τ₄ ≡ τ₁ ⇃[ ⦗ ρ⃨ ◆ ι₀ , ι₁ ◆ ρ ⦘ ]⇂
                lem-2 = {!!}

                lem-3 : isTypedℒHM (νs₄ ⊩ (νs₄ₓ ∷ Q , τ₁ ⇃[ ⦗ ρ⃨ ◆ ι₀ , ι₁ ◆ ρ ⦘ ]⇂ ∷ Γ₄) ⊢ α₄) se
                lem-3 = {!!}

                -- we can change the quantification to be over νs₁ₓ
                lem-4 : isTypedℒHM (νs₄ ⊩ (νs₁ₓ ∷ Q , τ₁ ⇃[ ⦗ ρ⃨ ◆ ι₀ , ι₁ ⦘ ]⇂ ∷ Γ₄) ⊢ α₄) se
                lem-4 = {!!}

                τ₁Γ₁<τ₁'Γ₄ : (τ₁ ∷ Γ₁) <Γ (τ₁ ⇃[ ⦗ ρ⃨ ◆ ι₀ , ι₁ ⦘ ]⇂ ∷ Γ₄)
                τ₁Γ₁<τ₁'Γ₄ = record { fst = ρ⃨ ; snd = {!!} }

                Ω₁R = Ω₁ (νs₄ ⊩ _ , _ , τ₁Γ₁<τ₁'Γ₄ , lem-4)
                -- (νs₄ ⊩ (τ₁ ⇃[ ⦗ ρ ◆ ι₀ , ι₁ ⦘ ]⇂) ∷ Γ₄ , α₄ , {!!} , {!τ₄Γ₄⊢α₄!})


                σ₂₄ : νs₂ ⟶ νs₄
                σ₂₄ = tiSub Ω₁R

                lem-20 : σᵤ₂ ◆ σ₂₄ ∼ σᵤ₄
                lem-20 = σᵤ₁ ◆ σ₁₂ ◆ σ₂₄    ⟨ assoc-l-◆ {f = σᵤ₁} {g = σ₁₂} {h = σ₂₄} ⟩-∼ -- ⟨ refl ◈ subProof Ω₁R ⟩-∼
                         σᵤ₁ ◆ (σ₁₂ ◆ σ₂₄)  ⟨ refl {x = σᵤ₁} ◈ subProof Ω₁R ⟩-∼
                         σᵤ₁ ◆ ρ⃨            ⟨ {!!} ⟩-∼
                         σᵤ₀ ◆  ◆ ρ⃨            ⟨ {!!} ⟩-∼
                         σᵤ₄                ∎

                -- lem-20 : α\


        --------------------------------------
        -- putting success and error case together

        resn = case res of
                {!!}
                success
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
          lem-5 : α₂ ⇃[ σ₂₃ ]⇂ ≡ (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂
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


          lem-6 : Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ ≡ Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
          lem-6 = Γ₂ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₂₃ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ₂} {f = ι₀} {σ₂₃} ⟩-≡
                  Γ₂ ⇃[ ι₀ ◆ σ₂₃ ]⇂ᶜ       ⟨ Γ₂ ⇃[≀ lem-0 ≀]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                  Γ₂ ⇃[ σᵃ₂₃ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ∎-≡

          -------------
          -- lift the typing of se and te to νs₃

          sp₃ : isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ β₃) se
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

          tp₃ : isTypedℒHM (νs₃ ⊩ (_ , Γ₃ ⇃[ ι₀ ]⇂ᶜ) ⊢ (β₃ ⇒ γ₃)) te
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

          -- this shows that we do have the typing instance
          𝑇 : CtxTypingInstance Γ (app te se)
          𝑇 = νs₃ₐ / νs₃ₓ ⊩ Γ₃ , γ₃ , Γ<Γ₃ , (app tp₃ sp₃)

  {-


          isInitial:𝑇 : ∀(𝑆 : CtxTypingInstance Γ (app te se)) -> 𝑇 <TI 𝑆
          isInitial:𝑇 (νs₄ ⊩ Ξ , ξ , Γ<Ξ , app {α = ξ₄} {β = ζ₄} Ξ⊢ξ⇒ζ Ξ⊢ξ) =
              record { tiSub = σ₃₄ ; typProof = lem-30 ; subProof = lem-20 }
            where
              σᵤ₄ : νs ⟶ νs₄
              σᵤ₄ = fst Γ<Ξ

              ΩR₀ = Ω₀ (νs₄ ⊩ Ξ , (ξ₄ ⇒ ζ₄) , Γ<Ξ , Ξ⊢ξ⇒ζ)

              σ₀₄ : νs₀ ⟶ νs₄
              σ₀₄ = tiSub ΩR₀

              Γ₀<Ξ : Γ₀ <Γ Ξ
              Γ₀<Ξ = record { fst = σ₀₄ ; snd = ctxProofTI ΩR₀ }

              ΩR₁ = Ω₁ (νs₄ ⊩ Ξ , ξ₄ , Γ₀<Ξ , Ξ⊢ξ)

              σ₁₄ : νs₁ ⟶ νs₄
              σ₁₄ = tiSub ΩR₁

              -------
              -- we can build a substitution from νs₂ by mapping γ to ζ₄
              --
              σₜ₄ : st ⟶ νs₄
              σₜ₄ = ⧜subst (incl ζ₄)

              σ₂₄ : νs₂ ⟶ νs₄
              σ₂₄ = ⦗ σ₁₄ , σₜ₄ ⦘
              --
              ------

              -- we know that under this substitution,
              -- u = α₂ and v = β₂ ⇒ γ₂ become both ξ⇒ζ
              lem-11 : u ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
              lem-11 = α₁ ⇃[ ι₀ ]⇂ ⇃[ σ₂₄ ]⇂        ⟨ §-HM-Proofs.prop-3 σ₁₄ σₜ₄ α₁ ⟩-≡
                      α₁ ⇃[ σ₁₄ ]⇂                 ⟨ refl-≡ ⟩-≡
                      α₀ ⇃[ σ₀₁ ]⇂ ⇃[ σ₁₄ ]⇂       ⟨ functoriality-◆-⇃[]⇂ {τ = α₀} {f = σ₀₁} {σ₁₄} ⟩-≡
                      α₀ ⇃[ σ₀₁ ◆ σ₁₄ ]⇂           ⟨ α₀ ⇃[≀ subProof ΩR₁ ≀]⇂ ⟩-≡
                      α₀ ⇃[ σ₀₄ ]⇂                 ⟨ typProof ΩR₀ ⟩-≡
                      ξ₄ ⇒ ζ₄                    ∎-≡

              -- we show how β₂ and γ₂ evaluate under σ₂₄
              lem-12a : β₂ ⇃[ σ₂₄ ]⇂ ≡ ξ₄
              lem-12a = β₂ ⇃[ σ₂₄ ]⇂            ⟨ refl-≡ ⟩-≡
                        β₁ ⇃[ σ₁₂ ]⇂ ⇃[ σ₂₄ ]⇂  ⟨ §-HM-Proofs.prop-3 σ₁₄ σₜ₄ β₁ ⟩-≡
                        β₁ ⇃[ σ₁₄ ]⇂            ⟨ typProof ΩR₁ ⟩-≡
                        ξ₄                      ∎-≡

              lem-12b : γ₂ ⇃[ σ₂₄ ]⇂ ≡ ζ₄
              lem-12b = γ₂ ⇃[ σ₂₄ ]⇂           ⟨ refl-≡ ⟩-≡
                      γᵇₜ ⇃[ ι₁ ]⇂ ⇃[ σ₂₄ ]⇂  ⟨ §-HM-Proofs.prop-4 σ₁₄ σₜ₄ γᵇₜ ⟩-≡
                      γᵇₜ ⇃[ σₜ₄ ]⇂           ∎-≡

              lem-12 : v ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
              lem-12 = λ i -> lem-12a i ⇒ lem-12b i

              -- taken together
              lem-13 : (asArr u) ◆ σ₂₄ ∼ (asArr v) ◆ σ₂₄
              lem-13 = cong-Str ⧜subst (cong-Str incl (≡→≡-Str (trans-Path lem-11 (sym-Path lem-12))))

              -- ... thus we can use the universal property
              -- to get νs₃ ⟶ νs₄
              σ₃₄ : νs₃ ⟶ νs₄
              σ₃₄ = ⦗ σ₂₄ , lem-13 ⦘₌

              -- and we know that
              lem-20 : σᵤ₃ ◆ σ₃₄ ∼ σᵤ₄
              lem-20 = σᵤ₂ ◆ σ₂₃ ◆ σ₃₄             ⟨ assoc-l-◆ {f = σᵤ₂} {σ₂₃} {σ₃₄} ⟩-∼
                      σᵤ₂ ◆ (σ₂₃ ◆ σ₃₄)           ⟨ refl {x = σᵤ₂} ◈ reduce-π₌ {p = lem-13} ⟩-∼
                      σᵤ₂ ◆ σ₂₄                   ⟨ refl ⟩-∼
                      σᵤ₁ ◆ ι₀ ◆ ⦗ σ₁₄ , σₜ₄ ⦘    ⟨ assoc-l-◆ {f = σᵤ₁} {ι₀} {σ₂₄} ⟩-∼
                      σᵤ₁ ◆ (ι₀ ◆ ⦗ σ₁₄ , σₜ₄ ⦘)  ⟨ refl {x = σᵤ₁} ◈ reduce-ι₀ {f = σ₁₄} {g = σₜ₄} ⟩-∼
                      σᵤ₁ ◆ σ₁₄                   ⟨ refl ⟩-∼
                      σᵤ₀ ◆ σ₀₁ ◆ σ₁₄             ⟨ assoc-l-◆ {f = σᵤ₀} {σ₀₁} {σ₁₄} ⟩-∼
                      σᵤ₀ ◆ (σ₀₁ ◆ σ₁₄)           ⟨ refl {x = σᵤ₀} ◈ subProof ΩR₁ ⟩-∼
                      σᵤ₀ ◆ σ₀₄                   ⟨ subProof ΩR₀ ⟩-∼
                      σᵤ₄                         ∎

              -- and finally how γ₃ evaluates under σ₃₄
              lem-30 : γ₃ ⇃[ σ₃₄ ]⇂ ≡ ζ₄
              lem-30 = γ₂ ⇃[ σ₂₃ ]⇂ ⇃[ σ₃₄ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = γ₂} {f = σ₂₃} {σ₃₄} ⟩-≡
                      γ₂ ⇃[ σ₂₃ ◆ σ₃₄ ]⇂        ⟨ γ₂ ⇃[≀ reduce-π₌ {p = lem-13} ≀]⇂ ⟩-≡
                      γ₂ ⇃[ σ₂₄ ]⇂              ⟨ lem-12b ⟩-≡
                      ζ₄                        ∎-≡
-}

-}
-------------------------------------------------------


-- the case of a lambda
γ {μs} {k} {Q = Q} Γ (lam te) = {!!} -- resn
{-
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
    success ((μs₁ₐ / μs₁ₓ ⊩ (α₁ ∷ Γ₁) , β₁ , α₀Γ₀<α₁Γ₁ , α₁Γ₁⊢β₁) , Ω) = 𝑇 , {!!} -- 𝑇 , isInitial:𝑇
      where
        σᵃ₀₁ : μs₀ ⟶ μs₁ₐ
        σᵃ₀₁ = α₀Γ₀<α₁Γ₁ .fst

        -- σᵤ₁ : μs ⟶ μs₁
        -- σᵤ₁ = σ₀ ◆ σ₀₁

        Γ<Γ₁ : Γ <Γ Γ₁
        Γ<Γ₁ = Γ<Γ₀ ⟡ tail-SomeℒHMCtx α₀Γ₀<α₁Γ₁

        𝑇 : CtxTypingInstance Γ (lam te)
        𝑇 = μs₁ₐ / μs₁ₓ ⊩ Γ₁ , _ , Γ<Γ₁ , lam α₁Γ₁⊢β₁

        isInitial:𝑇 : (𝑆 : CtxTypingInstance Γ (lam te)) -> 𝑇 <TI 𝑆
        isInitial:𝑇 (μs₂ ⊩ Γ₂ , .(_ ⇒ _) , Γ<Γ₂ , lam {α = α₂} {β = β₂} Γ₂α₂⊢β₂) =
          record { tiSub = σ₁₂ ; typProof = lem-30 ; subProof = lem-40 }

          where
            σᵤ₂ : μs ⟶ μs₂
            σᵤ₂ = Γ<Γ₂ .fst

            σₜ₂ : st ⟶ μs₂
            σₜ₂ = ⧜subst (incl α₂) ◆ ⦗ id , elim-⊥ ⦘

            -- μs ⊔ st = μs₀
            σ₀₂ : (μs ⊔ st) ⟶ μs₂
            σ₀₂ = ⦗ σᵤ₂ , σₜ₂ ⦘

            lem-5 : Γ₀ ⇃[ σ₀₂ ]⇂ᶜ ≡ Γ₂
            lem-5 = Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ₀₂ ]⇂ᶜ  ⟨ §-HM-Proofs.prop-2 σᵤ₂ σₜ₂ Γ ⟩-≡
                    Γ ⇃[ σᵤ₂ ]⇂ᶜ                  ⟨ Γ<Γ₂ .snd ⟩-≡
                    Γ₂                                  ∎-≡

            lem-10 : (α₀ ∷ Γ₀) ⇃[ σ₀₂ ]⇂ᶜ ≡ (α₂ ∷ Γ₂)
            lem-10 = λ i → §-HM-Proofs.prop-1 α₂ σ₀₂ i ∷ lem-5 i

            α₀Γ₀<α₂Γ₂ : (α₀ ∷ Γ₀) <Γ (α₂ ∷ Γ₂)
            α₀Γ₀<α₂Γ₂ = record { fst = σ₀₂ ; snd = lem-10 }

            ΩR = Ω (μs₂ ⊩ (α₂ ∷ Γ₂) , β₂ , α₀Γ₀<α₂Γ₂ , Γ₂α₂⊢β₂)

            σ₁₂ : μs₁ ⟶ μs₂
            σ₁₂ = tiSub ΩR

            lem-21 : (α₁ ∷ Γ₁) ⇃[ σ₁₂ ]⇂ᶜ ≡ α₂ ∷ Γ₂
            lem-21 = ctxProofTI ΩR

            lem-24 : α₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂ ≡ α₂
            lem-24 = λ i → split-DDList (lem-21 i) .fst

            lem-25 : α₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ≡ α₂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂
            lem-25 = cong _⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ lem-24

            lem-26 : α₁ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ σ₁₂ ]⇂ ≡ α₂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂
            lem-26 = α₁ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ σ₁₂ ]⇂          ⟨ functoriality-◆-⇃[]⇂ {τ = α₁} {f = ⦗ id , elim-⊥ ⦘} {g = σ₁₂} ⟩-≡
                    α₁ ⇃[ ⦗ id , elim-⊥ ⦘ ◆ σ₁₂ ]⇂              ⟨ α₁ ⇃[≀ §-HM-Helpers.prop-1 {f = σ₁₂} ≀]⇂ ⟩-≡
                    α₁ ⇃[ (σ₁₂ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ]⇂     ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α₁} {f = σ₁₂ ⇃⊔⇂ id} {g = ⦗ id , elim-⊥ ⦘}) ⟩-≡
                    α₁ ⇃[ (σ₁₂ ⇃⊔⇂ id) ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⟨ lem-25 ⟩-≡
                    α₂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂                 ∎-≡

            lem-29 : β₁ ⇃[ σ₁₂ ]⇂ ≡ β₂
            lem-29 = typProof ΩR

            lem-30 : (α₁ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β₁) ⇃[ σ₁₂ ]⇂ ≡ (α₂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β₂)
            lem-30 = λ i → lem-26 i ⇒ lem-29 i

            lem-40 : σᵤ₁ ◆ σ₁₂ ∼ σᵤ₂
            lem-40 = (σ₀ ◆ σ₀₁) ◆ σ₁₂   ⟨ assoc-l-◆ {f = σ₀} {σ₀₁} {σ₁₂} ⟩-∼
                     σ₀ ◆ (σ₀₁ ◆ σ₁₂)   ⟨ refl {x = σ₀} ◈ subProof ΩR ⟩-∼
                     σ₀ ◆ σ₀₂           ⟨ reduce-ι₀ {g = σₜ₂} ⟩-∼
                     σᵤ₂                ∎


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


