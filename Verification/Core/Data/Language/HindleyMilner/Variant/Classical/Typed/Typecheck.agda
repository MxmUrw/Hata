
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
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
open import Verification.Core.Data.Language.HindleyMilner.Helpers

open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Set.Decidable
open import Verification.Core.Order.Preorder

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition



record CtxTypingInstance {μs k} {Q : ℒHMQuant k} (Γ : ℒHMCtxFor Q μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _⊩_,_,_,_
  field metas : ℒHMTypes
  field ctx : ℒHMCtxFor Q metas
  field typ : ℒHMType (⟨ metas ⟩)
  field isInstance : Γ <Γ ctx
  field hasType : isTypedℒHM (metas ⊩ (Q , ctx) ⊢ typ) te

open CtxTypingInstance public


module _ {μs k} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μs} {te : UntypedℒHM k}  where
  record _<TI_ (𝑇 𝑆 : CtxTypingInstance Γ te) : 𝒰₀ where
    field tiSub : metas 𝑇 ⟶ metas 𝑆
    field typProof : typ 𝑇 ⇃[ tiSub ]⇂ ≡ typ 𝑆
    field subProof : isInstance 𝑇 .fst ◆ tiSub ∼ isInstance 𝑆 .fst

    ctxProofTI : ctx 𝑇 ⇃[ tiSub ]⇂-CtxFor ≡ ctx 𝑆
    ctxProofTI = {!!}

  open _<TI_ public

InitialCtxTypingInstance : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtxFor Q μs) (te : UntypedℒHM k) -> 𝒰₀
InitialCtxTypingInstance Γ te = ∑ λ (𝑇 : CtxTypingInstance Γ te) -> ∀(𝑆 : CtxTypingInstance Γ te) -> 𝑇 <TI 𝑆




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

      α₀ = α ⇃[ id ⇃⊔⇂ id ]⇂

      Γ₀ = Γ ⇃[ ι₀ ]⇂-CtxFor

      Γ<Γ₀ : Γ <Γ Γ₀
      Γ<Γ₀ = record { fst = σᵤ₀ ; snd = refl-≡ }

  in right (((μs ⊔ vα) ⊩ Γ₀ , α₀ , Γ<Γ₀ , var k∍i refl-≣ id)


           -- now we have to prove that this is the "initial" such typing instance
           , λ {(.(μs₁ ⊔ vα₁) ⊩ Γ₁ , α₁ , Γ<Γ₁ , var {μs = μs₁} {Γ = Γ₁'} _ {vα' = vα₁} refl-≣ ρ) →

               -- given another instance, which has to use `var` to prove the typing

                let σᵤ₁ : μs ⟶ μs₁ ⊔ vα₁
                    σᵤ₁ = Γ<Γ₁ .fst

                    σ₀₁ : μs ⊔ vα ⟶ μs₁ ⊔ vα₁
                    σ₀₁ = ⦗ σᵤ₁ , (ρ ◆ ι₁) ⦘

                    --------------------------------------
                    -- next, we need to show that this
                    -- substitution recreates the given Δ and δ

                    -------------
                    -- i) for σ₀₁
                    -------------

                    lem-10 : σᵤ₀ ◆ σ₀₁ ∼ σᵤ₁
                    lem-10 = reduce-ι₀ {g = ρ ◆ ι₁}

                    -------------
                    -- ii) for α₀
                    -------------

                    lem-11 : α₀ ≡ α
                    lem-11 = α ⇃[ id ⇃⊔⇂ id ]⇂    ⟨ α ⇃[≀ functoriality-id-⊔ ≀]⇂ ⟩-≡
                              α ⇃[ id ]⇂           ⟨ functoriality-id-⇃[]⇂ {τ = α} ⟩-≡
                              α                    ∎-≡

                    lem-12 : α₀ ⇃[ σ₀₁ ]⇂ ≡ lookup-Listᴰ² Γ₁ k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂
                    lem-12 = α ⇃[ id ⇃⊔⇂ id ]⇂ ⇃[ σ₀₁ ]⇂     ⟨ cong _⇃[ σ₀₁ ]⇂ lem-11 ⟩-≡
                              lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σᵤ₁ , ρ ◆ ι₁ ⦘ ]⇂  ⟨ sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i σᵤ₁ (ρ ◆ ι₁)) ⟩-≡
                              lookup-Listᴰ² (Γ ⇃[ σᵤ₁ ]⇂-CtxFor) k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂

                              ⟨ (λ i -> lookup-Listᴰ² (Γ<Γ₁ .snd i ) k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂) ⟩-≡

                              lookup-Listᴰ² Γ₁ k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂                     ∎-≡


                    lem-15 : Γ₁' ⇃[ id ◆ ι₀ ]⇂-CtxFor ≡ Γ₁
                    lem-15 = Γ₁' ⇃[ id ◆ ι₀ ]⇂-CtxFor  ⟨ Γ₁' ⇃[≀ unit-l-◆ ≀]⇂-CtxFor ⟩-≡
                             Γ₁' ⇃[ ι₀ ]⇂-CtxFor       ∎-≡

                    lem-16 : α₁ ≡ lookup-Listᴰ² Γ₁ k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂
                    lem-16 = lookup-Listᴰ² Γ₁' k∍i ⇃[ ⦗ id ◆ ι₀ , ρ ◆ ι₁ ⦘ ]⇂   ⟨ sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ₁'} k∍i (id ◆ ι₀) (ρ ◆ ι₁)) ⟩-≡
                              lookup-Listᴰ² (Γ₁' ⇃[ id ◆ ι₀ ]⇂-CtxFor) k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂

                              ⟨ (λ i -> lookup-Listᴰ² (lem-15 i) k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂) ⟩-≡

                              lookup-Listᴰ² (Γ₁) k∍i ⇃[ ⦗ id , ρ ◆ ι₁ ⦘ ]⇂                       ∎-≡

                    lem-20 : α₀ ⇃[ σ₀₁ ]⇂ ≡ α₁
                    lem-20 = trans-Path lem-12 (sym-Path lem-16)

                in record { tiSub = σ₀₁ ; typProof = lem-20 ; subProof = lem-10 }

               })
-}
γ {μs = νs} {Q = Q} Γ (slet te se) with γ Γ te
... | (left _) = {!!}
... | (right ((νs₀ ⊩ Γ₀ , τ₀ , Γ<Γ₀ , Γ₀⊢τ₀), Ω₀)) = (withAbstr (abstr-Ctx Γ₀ τ₀))
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

            -- Γ₁ₓ = Γ₀ ⇃[ σ₀₁ₓ ]⇂-CtxFor
            -- τ₁ₓ = τ₀ ⇃[ σ₀₁ₓ ]⇂

            -- Γ₁ₓ⊢τ₁ₓ : isTypedℒHM (νs₁ ⊔ νs₁ₓ ⊩ (_ , Γ₁ₓ) ⊢ τ₁ₓ) te
            -- Γ₁ₓ⊢τ₁ₓ = §-isTypedℒHM.prop-2 σ₀₁ₓ Γ₀⊢τ₀

            isAbstr₀,₁' : isAbstr νs₁ₓ Γ₀ (Γ₁ ⇃[ σ₁₂ ]⇂-CtxFor) τ₀ (τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂) --  Γ₁ₓ τ₀ τ₁ₓ
            isAbstr₀,₁' = §-isAbstr.prop-1 σ₁₂ isAb

            isAbstr₀,₂ : isAbstr νs₁ₓ Γ₀ (Γ₂) τ₀ (τ₂) --  Γ₁ₓ τ₀ τ₁ₓ
            isAbstr₀,₂ = transport (λ i -> isAbstr νs₁ₓ Γ₀ (Γ₁₂ i) τ₀ (τ₁₂ i)) isAbstr₀,₁'
              where
                Γ₁₂ : Γ₁ ⇃[ σ₁₂ ]⇂-CtxFor ≡ Γ₂
                Γ₁₂ = λ i -> split-Listᴰ² (τ₁Γ₁<τ₂Γ₂ .snd i) .snd

                τ₁₂ : τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂ ≡ τ₂
                τ₁₂ = λ i -> split-Listᴰ² (τ₁Γ₁<τ₂Γ₂ .snd i) .fst

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
                         σᵤ₁ ◆ (σ₁₂ ◆ σ₂₄)  ⟨ refl {a = σᵤ₁} ◈ subProof Ω₁R ⟩-∼
                         σᵤ₁ ◆ ρ⃨            ⟨ {!!} ⟩-∼
                         σᵤ₀ ◆  ◆ ρ⃨            ⟨ {!!} ⟩-∼
                         σᵤ₄                ∎

                -- lem-20 : α\


        --------------------------------------
        -- putting success and error case together

        resn = case res of
                {!!}
                success


{-
  let νs₀' , Γ₀' , τ₀' , isAb = abstr-Ctx Γ₀⊢τ₀

      ϕ = metasProof isAb

      κs = τ₀' .fst

      -- add the type τ₀' to the context
      -- and typecheck se
      x = γ (τ₀' ∷ Γ₀') se

  in case x of
        {!!}

        -- if we get a good result
        λ {(μs ⊩ (τ₁ ∷ Γ₁) , β , Γ₁<τ₀Γ , Γ₁⊢τ₁) →

          let σ = fst Γ₁<τ₀Γ

              Γ₀v = Γ₀ ⇃[ ⟨ ϕ ⟩⁻¹ ◆ (σ ⇃⊔⇂ id) ]⇂-Ctx
              τ₀v = τ₀ ⇃[ ⟨ ϕ ⟩⁻¹ ◆ (σ ⇃⊔⇂ id) ]⇂

              tepv : isTypedℒHM ((μs ⊔ ι κs) ⊩ Γ₀v ⊢ τ₀v) te
              tepv = §-isTypedℒHM.prop-2 _ Γ₀⊢τ₀

              abPv : isAbstr (ι (τ₁ .fst)) Γ₀v Γ₁ τ₀v (τ₁ .snd)
              abPv =
                let
                    lem-1 : μs ⊔ ι (τ₁ .fst) ≅ (μs ⊔ ι κs)
                    lem-1 = {!!} -- but we know that actually ι (τ₁.fst) ≡ ι κs
                                 -- since they both come from the quantified part of the context
                in record { metasProof = lem-1 ; ctxProof = {!!} ; typeProof = {!!} }

          in right (μs ⊩ Γ₁ , β , {!!} , slet abPv tepv Γ₁⊢τ₁)
        }
-}

-- the case of an application
γ {μs = νs} Γ (app te se) = {!!} -- with γ Γ te
{-
... | (left _) = {!!}
... | (right ((νs₀ ⊩ Γ₀ , α₀ , Γ<Γ₀ , Γ₀⊢α₀), Ω₀)) with γ Γ₀ se
... | (left _) = {!!}
... | (right ((νs₁ ⊩ Γ₁ , β₁ , Γ₀<Γ₁ , Γ₁⊢β₁), Ω₁)) = (resn res)
  where

    σᵤ₀ : _ ⟶ νs₀
    σᵤ₀ = fst Γ<Γ₀

    -- lift the τ0 typing to Γ₁
    σ₀₁ : νs₀ ⟶ νs₁
    σ₀₁ = fst Γ₀<Γ₁

    σᵤ₁ : νs ⟶ νs₁
    σᵤ₁ = σᵤ₀ ◆ σ₀₁

    -- we lift α₀ to the metas νs₁
    -- τ₀'
    α₁ : ℒHMType _
    α₁ = α₀ ⇃[ σ₀₁ ]⇂

    -- and the typing of the term `te`
    Γ₁⊢α₁' : isTypedℒHM (νs₁ ⊩ (_ , Γ₀ ⇃[ σ₀₁ ]⇂-CtxFor) ⊢ α₁) te
    Γ₁⊢α₁' = §-isTypedℒHM.prop-2 σ₀₁ Γ₀⊢α₀

    Γ₁⊢α₁ : isTypedℒHM (νs₁ ⊩ (_ , Γ₁) ⊢ α₁) te
    Γ₁⊢α₁ = transport (λ i -> isTypedℒHM (νs₁ ⊩ (_ , (Γ₀<Γ₁ .snd i)) ⊢ α₁) te) Γ₁⊢α₁'

    -- we need a new type variable for the return
    -- type of the application, so we move to νs₂
    νs₂ = (νs₁) ⊔ st
    σ₁₂ : νs₁ ⟶ νs₂
    σ₁₂ = ι₀

    σᵤ₂ : νs ⟶ νs₂
    σᵤ₂ = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂

    -- τ₀''
    α₂ : ℒHMType ⟨ νs₂ ⟩
    α₂ = α₁ ⇃[ σ₁₂ ]⇂

    β₂ : ℒHMType ⟨ νs₂ ⟩
    β₂ = β₁ ⇃[ σ₁₂ ]⇂

    -- Γ₁'
    Γ₂ = Γ₁ ⇃[ σ₁₂ ]⇂-CtxFor

    -- we call the new type γ
    γₜ : ℒHMType ⟨ st ⟩
    γₜ = var incl

    γ₂ : ℒHMType ⟨ νs₂ ⟩
    γ₂ = γₜ ⇃[ ι₁ ]⇂

    -- the types which we unify are:
    u : ℒHMType ⟨ νs₂ ⟩
    u = α₂

    v : ℒHMType ⟨ νs₂ ⟩
    v = β₂ ⇒ γ₂

    res = unify-ℒHMTypes (asArr u) (asArr v)

    resn : (¬ hasCoequalizerCandidate (asArr u , asArr v)) +-𝒰 (hasCoequalizer (asArr u) (asArr v))
           -> (CtxTypingInstance Γ (app te se) -> ⊥-𝒰 {ℓ₀}) + InitialCtxTypingInstance Γ (app te se)
    resn (left _) = {!!}
    resn (right x) = right (𝑇 , isInitial:𝑇)
      where
        νs₃ = ⟨ x ⟩
        σ₂₃ : νs₂ ⟶ νs₃
        σ₂₃ = π₌

        β₃ = β₂ ⇃[ σ₂₃ ]⇂
        γ₃ = γ₂ ⇃[ σ₂₃ ]⇂
        Γ₃ = Γ₂ ⇃[ σ₂₃ ]⇂-CtxFor

        -- thus the full substitution we need is the following
        σᵤ₃ = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂ ◆ σ₂₃

        lem-1 : Γ ⇃[ σᵤ₀ ◆ σ₀₁ ]⇂-CtxFor ≡ Γ₁
        lem-1 = Γ ⇃[ σᵤ₀ ◆ σ₀₁ ]⇂-CtxFor             ⟨ sym-Path (functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ} {f = σᵤ₀} {σ₀₁})  ⟩-≡
                Γ ⇃[ σᵤ₀ ]⇂-CtxFor ⇃[ σ₀₁ ]⇂-CtxFor  ⟨ cong _⇃[ σ₀₁ ]⇂-CtxFor (Γ<Γ₀ .snd) ⟩-≡
                Γ₀ ⇃[ σ₀₁ ]⇂-CtxFor                  ⟨ Γ₀<Γ₁ .snd ⟩-≡
                Γ₁                                   ∎-≡

        lem-2 : Γ ⇃[ σᵤ₀ ◆ σ₀₁ ◆ σ₁₂ ◆ σ₂₃ ]⇂-CtxFor ≡ Γ₃
        lem-2 = Γ ⇃[ σᵤ₀ ◆ σ₀₁ ◆ σ₁₂ ◆ σ₂₃ ]⇂-CtxFor                         ⟨ sym-Path (functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ} {f = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂} {σ₂₃}) ⟩-≡
                Γ ⇃[ σᵤ₀ ◆ σ₀₁ ◆ σ₁₂ ]⇂-CtxFor ⇃[ σ₂₃ ]⇂-CtxFor              ⟨ cong _⇃[ σ₂₃ ]⇂-CtxFor (sym-Path (functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ} {f = σᵤ₀ ◆ σ₀₁} {σ₁₂})) ⟩-≡
                Γ ⇃[ σᵤ₀ ◆ σ₀₁ ]⇂-CtxFor ⇃[ σ₁₂ ]⇂-CtxFor ⇃[ σ₂₃ ]⇂-CtxFor   ⟨ cong (λ ξ -> ξ ⇃[ σ₁₂ ]⇂-CtxFor ⇃[ σ₂₃ ]⇂-CtxFor) lem-1 ⟩-≡
                Γ₁ ⇃[ σ₁₂ ]⇂-CtxFor ⇃[ σ₂₃ ]⇂-CtxFor                         ∎-≡

        Γ<Γ₃ : Γ <Γ Γ₃
        Γ<Γ₃ = record { fst = σᵤ₃ ; snd = lem-2 }

        -- we know that under `σ₂₃` both α₂ and `β₂ ⇒ γ₂` are the same
        lem-5 : α₂ ⇃[ σ₂₃ ]⇂ ≡ (β₂ ⇒ γ₂) ⇃[ σ₂₃ ]⇂
        lem-5 = let x = lem-5a
                    y = cong-Str ⟨_⟩ x
                    z = cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 y
                    q = ≡-Str→≡ z
                in q
          where
            lem-5a : (asArr α₂) ◆ σ₂₃ ∼ (asArr (β₂ ⇒ γ₂)) ◆ σ₂₃
            lem-5a = equate-π₌

        -- lift the typing to Γ₃
        sp₃ : isTypedℒHM (νs₃ ⊩ (_ , Γ₃) ⊢ β₃) se
        sp₃ = §-isTypedℒHM.prop-2 σ₂₃ (§-isTypedℒHM.prop-2 σ₁₂ Γ₁⊢β₁)

        tp₃' : isTypedℒHM (νs₃ ⊩ (_ , Γ₃) ⊢ (α₂ ⇃[ σ₂₃ ]⇂)) te
        tp₃' = §-isTypedℒHM.prop-2 σ₂₃ (§-isTypedℒHM.prop-2 σ₁₂ Γ₁⊢α₁)

        tp₃ : isTypedℒHM (νs₃ ⊩ (_ , Γ₃) ⊢ (β₃ ⇒ γ₃)) te
        tp₃ = transport (λ i -> isTypedℒHM (νs₃ ⊩ (_ , Γ₃) ⊢ (lem-5 i)) te) tp₃'

        -- this shows that we do have the typing instance
        𝑇 : CtxTypingInstance Γ (app te se)
        𝑇 = (νs₃ ⊩ Γ₃ , γ₃ , Γ<Γ₃ , app tp₃ sp₃ )


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
                     γₜ ⇃[ ι₁ ]⇂ ⇃[ σ₂₄ ]⇂  ⟨ §-HM-Proofs.prop-4 σ₁₄ σₜ₄ γₜ ⟩-≡
                     γₜ ⇃[ σₜ₄ ]⇂           ∎-≡

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
                     σᵤ₂ ◆ (σ₂₃ ◆ σ₃₄)           ⟨ refl {a = σᵤ₂} ◈ reduce-π₌ {p = lem-13} ⟩-∼
                     σᵤ₂ ◆ σ₂₄                   ⟨ refl ⟩-∼
                     σᵤ₁ ◆ ι₀ ◆ ⦗ σ₁₄ , σₜ₄ ⦘    ⟨ assoc-l-◆ {f = σᵤ₁} {ι₀} {σ₂₄} ⟩-∼
                     σᵤ₁ ◆ (ι₀ ◆ ⦗ σ₁₄ , σₜ₄ ⦘)  ⟨ refl {a = σᵤ₁} ◈ reduce-ι₀ {f = σ₁₄} {g = σₜ₄} ⟩-∼
                     σᵤ₁ ◆ σ₁₄                   ⟨ refl ⟩-∼
                     σᵤ₀ ◆ σ₀₁ ◆ σ₁₄             ⟨ assoc-l-◆ {f = σᵤ₀} {σ₀₁} {σ₁₄} ⟩-∼
                     σᵤ₀ ◆ (σ₀₁ ◆ σ₁₄)           ⟨ refl {a = σᵤ₀} ◈ subProof ΩR₁ ⟩-∼
                     σᵤ₀ ◆ σ₀₄                   ⟨ subProof ΩR₀ ⟩-∼
                     σᵤ₄                         ∎

            -- and finally how γ₃ evaluates under σ₃₄
            lem-30 : γ₃ ⇃[ σ₃₄ ]⇂ ≡ ζ₄
            lem-30 = γ₂ ⇃[ σ₂₃ ]⇂ ⇃[ σ₃₄ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = γ₂} {f = σ₂₃} {σ₃₄} ⟩-≡
                     γ₂ ⇃[ σ₂₃ ◆ σ₃₄ ]⇂        ⟨ γ₂ ⇃[≀ reduce-π₌ {p = lem-13} ≀]⇂ ⟩-≡
                     γ₂ ⇃[ σ₂₄ ]⇂              ⟨ lem-12b ⟩-≡
                     ζ₄                        ∎-≡
-}


-------------------------------------------------------


{-
{-
    resn = case res of
           {!!}
           λ x →
             let νs₃ = ⟨ x ⟩
                 σ₂₃ : νs₂ ⟶ νs₃
                 σ₂₃ = π₌

                 β₃ = β₂ ⇃[ σ₂₃ ]⇂
                 Γ₃ = Γ₂ ⇃[ σ₂₃ ]⇂-Ctx

                 -- thus the full substitution we need is the following
                 σᵤ₃ = σᵤ₀ ◆ σ₀₁ ◆ σ₁₂ ◆ σ₂₃

                 Γ<Γ₃ : Γ <Γ Γ₃
                 Γ<Γ₃ = record { fst = σᵤ₃ ; snd = {!!} }

                 -- move the typing of se to Γ₂ = Γ₁[ ι₀ ◆ σ ]
                 sp : isTypedℒHM (νs₂ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx) ⊢ (τ₁ ⇃[ ι₀ ]⇂)) se
                 sp = §-isTypedℒHM.prop-2 ι₀ Γ₁⊢τ₁

                 sp' : isTypedℒHM (⟨ x ⟩ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx ⇃[ σ ]⇂-Ctx) ⊢ (τ₁ ⇃[ ι₀ ]⇂ ⇃[ σ ]⇂)) se
                 sp' = §-isTypedℒHM.prop-2 σ sp

                 -- move the typing of te to Γ₂ = Γ₀[ σᵤ₀ ◆ ι₀ ◆ σ ]
                 tp : isTypedℒHM (νs₁ ⊩ Γ₁ ⊢ (τ₀ ⇃[ σᵤ₀ ]⇂)) te
                 tp = {!!}

                 tp' : isTypedℒHM (νs₂ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx) ⊢ (τ₀ ⇃[ σᵤ₀ ]⇂ ⇃[ ι₀ ]⇂)) te
                 tp' = §-isTypedℒHM.prop-2 ι₀ tp

                 tp'' : isTypedℒHM (⟨ x ⟩ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx ⇃[ σ ]⇂-Ctx) ⊢ (τ₀ ⇃[ σᵤ₀ ]⇂ ⇃[ ι₀ ]⇂ ⇃[ σ ]⇂)) te
                 tp'' = §-isTypedℒHM.prop-2 σ tp'

                 tp''' : isTypedℒHM (⟨ x ⟩ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx ⇃[ σ ]⇂-Ctx) ⊢ (τ₁ ⇃[ ι₀ ]⇂ ⇃[ σ ]⇂ ⇒ β ⇃[ σ ]⇂)) te
                 tp''' = {!!}
-}

             in right ((νs₃ ⊩ Γ₃ , β₃ , Γ<Γ₃ , {!!} ), -- app tp''' sp'),
                      λ {(νs₄ ⊩ Ξ , ξ , Γ<Ξ , app {α = ξ₄} {β = ζ₄} Ξ⊢ξ⇒ζ Ξ⊢ξ) ->
                        let σᵤ₄ : νs ⟶ νs₄
                            σᵤ₄ = fst Γ<Ξ

                            ΩR₀ = Ω₀ (νs₄ ⊩ Ξ , (ξ₄ ⇒ ζ₄) , Γ<Ξ , Ξ⊢ξ⇒ζ)

                            σ₀₄ : νs₀ ⟶ νs₄
                            σ₀₄ = tiSub ΩR₀

                            Γ₀<Ξ : Γ₀ <Γ Ξ
                            Γ₀<Ξ = record { fst = σ₀₄ ; snd = ctxProof ΩR₀ }

                            ΩR₁ = Ω₁ (νs₄ ⊩ Ξ , ξ₄ , Γ₀<Ξ , Ξ⊢ξ)

                            σ₁₄ : νs₁ ⟶ νs₄
                            σ₁₄ = tiSub ΩR₁

                            -- we can build a substitution from νs₂ by mapping γ to ζ₄
                            σ₂₄ : νs₂ ⟶ νs₄
                            σ₂₄ = ⦗ σ₁₄ , ⧜subst (incl ζ₄) ⦘

                            -- we know that under this substitution,
                            -- u = α₂ and v = β₂ ⇒ γ₂ become both ξ⇒ζ
                            lem-1 : u ⇃[ σ₂₄ ]⇂ ≡ ξ₄ ⇒ ζ₄
                            lem-1 = α₁ ⇃[ ι₀ ]⇂ ⇃[ σ₂₄ ]⇂       ⟨ {!!} ⟩-≡
                                     α₁ ⇃[ ι₀ ◆ ⦗ σ₁₄ , _ ⦘ ]⇂   ⟨ {!!} ⟩-≡
                                     α₁ ⇃[ σ₁₄ ]⇂                ⟨ {!!} ⟩-≡
                                     α₀ ⇃[ σ₀₁ ]⇂ ⇃[ σ₁₄ ]⇂      ⟨ {!!} ⟩-≡
                                     α₀ ⇃[ σ₀₁ ◆ σ₁₄ ]⇂          ⟨ {!!} ⟩-≡
                                     α₀ ⇃[ σ₀₄ ]⇂                ⟨ typProof ΩR₀ ⟩-≡
                                     ξ₄ ⇒ ζ₄                    ∎-≡

                            -- ... thus we can use the universal property
                            -- to get νs₃ ⟶ νs₄
                            σ₃₄ : νs₃ ⟶ νs₄
                            σ₃₄ = {!!}

                            -- and we know that
                            lem-20 : σᵤ₃ ◆ σ₃₄ ∼ σᵤ₄
                            lem-20 = {!!}

                        in record { tiSub = σ₃₄ ; typProof = {!!} ; ctxProof = {!!} ; subProof = lem-20 }
                -}

{-
                      let ΩR₀ = Ω₀ (ζs ⊩ Ξ , (ξ₀ ⇒ ξ₁) , Γ?<Ξ , Ξ⊢ξ₀⇒ξ₁)

                          σᵤ₀ = tiSub ΩR₀

                          Γ₀<Ξ : Γ₀ <Γ Ξ
                          Γ₀<Ξ = record { fst = σᵤ₀ ; snd = ctxProof ΩR₀ }

                          ΩR₁ = Ω₁ (ζs ⊩ Ξ , ξ₀ , Γ₀<Ξ , Ξ⊢ξ₀)

                          σ₀₁ = tiSub ΩR₁

                          aa = τ₀'' ⇃[ σᵤ₀ ]⇂


                      in record { tiSub = {!!} ; typProof = {!!} ; ctxProof = {!!} }

                      })

-}
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
    Γ₀ = Γ ⇃[ ι₀ ]⇂-CtxFor

    σ₀ : μs ⟶ μs ⊔ st
    σ₀ = ι₀

    -- call typechecking recursively on `te`
    res = γ (α₀ ∷ Γ₀) te

    -- computing the initial typing instance
    -- assuming we have one for te
    success : InitialCtxTypingInstance (α₀ ∷ Γ₀) te -> InitialCtxTypingInstance Γ (lam te)
    success ((μs₁ ⊩ (α₁ ∷ Γ₁) , β₁ , α₀Γ₀<α₁Γ₁ , hastype) , Ω) = 𝑇 , isInitial:𝑇
      where
        σ₀₁ : μs₀ ⟶ μs₁
        σ₀₁ = α₀Γ₀<α₁Γ₁ .fst

        σᵤ₁ : μs ⟶ μs₁
        σᵤ₁ = σ₀ ◆ σ₀₁

        lem-1 : Γ ⇃[ σᵤ₁ ]⇂-CtxFor ≡ Γ₁
        lem-1 = Γ ⇃[ σᵤ₁ ]⇂-CtxFor                  ⟨ sym-Path (functoriality-◆-⇃[]⇂-CtxFor {Γ = Γ} {f = σ₀} {σ₀₁}) ⟩-≡
                Γ ⇃[ σ₀ ]⇂-CtxFor ⇃[ σ₀₁ ]⇂-CtxFor  ⟨ (λ i -> split-Listᴰ² (α₀Γ₀<α₁Γ₁ .snd i) .snd ) ⟩-≡
                Γ₁                                  ∎-≡

        Γ<Γ₁ : Γ <Γ Γ₁
        Γ<Γ₁ = record { fst = σᵤ₁ ; snd = lem-1 }

        𝑇 : CtxTypingInstance Γ (lam te)
        𝑇 = (μs₁ ⊩ Γ₁ , _ , Γ<Γ₁ , lam hastype)

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

            lem-5 : Γ₀ ⇃[ σ₀₂ ]⇂-CtxFor ≡ Γ₂
            lem-5 = Γ ⇃[ ι₀ ]⇂-CtxFor ⇃[ σ₀₂ ]⇂-CtxFor  ⟨ §-HM-Proofs.prop-2 σᵤ₂ σₜ₂ Γ ⟩-≡
                    Γ ⇃[ σᵤ₂ ]⇂-CtxFor                  ⟨ Γ<Γ₂ .snd ⟩-≡
                    Γ₂                                  ∎-≡

            lem-10 : (α₀ ∷ Γ₀) ⇃[ σ₀₂ ]⇂-CtxFor ≡ (α₂ ∷ Γ₂)
            lem-10 = λ i → §-HM-Proofs.prop-1 α₂ σ₀₂ i ∷ lem-5 i

            α₀Γ₀<α₂Γ₂ : (α₀ ∷ Γ₀) <Γ (α₂ ∷ Γ₂)
            α₀Γ₀<α₂Γ₂ = record { fst = σ₀₂ ; snd = lem-10 }

            ΩR = Ω (μs₂ ⊩ (α₂ ∷ Γ₂) , β₂ , α₀Γ₀<α₂Γ₂ , Γ₂α₂⊢β₂)

            σ₁₂ : μs₁ ⟶ μs₂
            σ₁₂ = tiSub ΩR

            lem-21 : (α₁ ∷ Γ₁) ⇃[ σ₁₂ ]⇂-CtxFor ≡ α₂ ∷ Γ₂
            lem-21 = ctxProofTI ΩR

            lem-24 : α₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂ ≡ α₂
            lem-24 = λ i → split-Listᴰ² (lem-21 i) .fst

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
                     σ₀ ◆ (σ₀₁ ◆ σ₁₂)   ⟨ refl {a = σ₀} ◈ subProof ΩR ⟩-∼
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






