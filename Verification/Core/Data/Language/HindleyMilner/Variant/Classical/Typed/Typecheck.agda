
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
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition

open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Set.Decidable

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition



record _<Γ_ {k} {μs νs} (Γ : ℒHMCtx' k μs) (Γ' : ℒHMCtx' k νs) : 𝒰₀ where
  field fst : μs ⟶ νs
  field snd : Γ ⇃[ fst ]⇂-Ctx ≡ Γ'
open _<Γ_ public

record CtxTypingInstance {μs k} (Γ : ℒHMCtx' k μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _⊩_,_,_,_
  field metas : ℒHMTypes
  field ctx : ℒHMCtx' k metas
  field typ : ℒHMType (⟨ metas ⟩)
  field isInstance : Γ <Γ ctx
  field hasType : isTypedℒHM (metas ⊩ ctx ⊢ typ) te

open CtxTypingInstance public

module _ {μs k} {Γ : ℒHMCtx' k μs} {te : UntypedℒHM k}  where
  record _<TI_ (𝑇 𝑆 : CtxTypingInstance Γ te) : 𝒰₀ where
    field tiSub : metas 𝑇 ⟶ metas 𝑆
    field typProof : typ 𝑇 ⇃[ tiSub ]⇂ ≡ typ 𝑆
    field ctxProof : ctx 𝑇 ⇃[ tiSub ]⇂-Ctx ≡ ctx 𝑆
    field subProof : isInstance 𝑇 .fst ◆ tiSub ∼ isInstance 𝑆 .fst

  open _<TI_ public


γ : ∀{μs k} -> (Γ : ℒHMCtx' k μs) -> (te : UntypedℒHM k)
  -> (CtxTypingInstance Γ te -> ⊥-𝒰 {ℓ₀})
    +
     (∑ λ (𝑇 : CtxTypingInstance Γ te) -> ∀(𝑆 : CtxTypingInstance Γ te) -> 𝑇 <TI 𝑆)
γ {μs} {k} Γ (var k∍i) =
{-
  let
      -- ∀[ vα ] α = lookup-DList Γ k∍i
      vα : ℒHMTypes
      vα = {!!}

      νs₀ : ℒHMTypes
      νs₀ = νs ⊔ vα

      σᵤ₀ : νs ⟶ νs ⊔ vα
      σᵤ₀ = ι₀

      -- Γ₀ = Γ ⇃[ σᵤ₀ ]⇂-Ctx

  in right (((νs₀) ⊩ (Γ ⇃[ σᵤ₀ ]⇂-Ctx) , {!!} , {!!} , {!!}) , {!!})

-}
  let ∀[ vα ] α = lookup-DList Γ k∍i
  in right (((μs ⊔ ι vα) ⊩ Γ ⇃[ ι₀ ]⇂-Ctx , α ⇃[ id ⇃⊔⇂ id ]⇂ , {!!} , var k∍i refl-≣ id)

           -- now we have to prove that this is the "initial" such typing instance
           , λ {(ξs ⊩ Δ , δ , Γ<Δ , var {μs = μs₁} {Γ = Γ₁} {vα' = vα'} _ refl-≣ σ) →
               -- given another instance, which has to use `var` to prove the typing

                 let
                     -- first we construct the substitution
                     -- for this, we have two relevant statements
                     --     Γ<Δ and (σ : ι vα'ᵇ ⟶ vα')
                     ρ : μs ⟶ μs₁ ⊔ vα'
                     ρ = Γ<Δ .fst

                     vα'ᵇ = lookup-DList Γ₁ k∍i

                     σ'ᵇ : ι vα ⟶ ι (vα'ᵇ .fst)
                     σ'ᵇ = {!⟨ ι∀∍ Γ k∍i ⟩⁻¹!}

                     tiσ : μs ⊔ ι vα ⟶ μs₁ ⊔ vα'
                     tiσ = ⦗ ρ , {!!} ◆ σ ◆ ι₁ ⦘

                     --------------------------------------
                     -- next, we need to show that this
                     -- substitution recreates the given Δ and δ

                     -------------
                     -- i) for Δ
                     -------------
                     lem-20 : Γ ⇃[ ι₀ ]⇂-Ctx ⇃[ tiσ ]⇂-Ctx ≡ Δ
                     lem-20 = {!!}
                     {-
                              Γ ⇃[ ι₀ ]⇂-Ctx ⇃[ tiσ ]⇂-Ctx ⟨ {!!} ⟩-≡ -- functoriality here
                              Γ ⇃[ ι₀ ◆ tiσ ]⇂-Ctx         ⟨ refl-≡ ⟩-≡
                              Γ ⇃[ ι₀ ◆ ⦗ ρ , σ'ᵇ ◆ σ ◆ ι₁ ⦘ ]⇂-Ctx   ⟨ Γ ⇃[≀ reduce-ι₀ {f = ρ} {g = σ'ᵇ ◆ σ ◆ ι₁} ≀]⇂-Ctx ⟩-≡
                              Γ ⇃[ ρ ]⇂-Ctx                ⟨ Γ<Δ .snd ⟩-≡
                              Δ                           ∎-≡
                     -}

                     -------------
                     -- ii) for δ
                     -------------

                     -- we know that looking up sth in Γ translates to
                     -- looking up sth in Δ

                     lem-01 : δ ≡ lookup-DList Γ₁ k∍i .snd ⇃[ id ⇃⊔⇂ σ ]⇂
                     lem-01 = refl-≡

{-
                     lem-02 : lookup-DList Γ₁ k∍i .snd ⇃[ id ⇃⊔⇂ σ ]⇂
                              ≡
                              lookup-DList (Γ₁ ⇃[ ι₀ ◆ (id ⇃⊔⇂ σ) ]⇂-Ctx) k∍i .snd
                                           ⇃[ ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘ ]⇂
                     lem-02 = §-ℒHMCtx.prop-1 {Γ = Γ₁} k∍i (id ⇃⊔⇂ σ)

                     lem-03a : Γ₁ ⇃[ ι₀ ◆ (id ⇃⊔⇂ σ) ]⇂-Ctx ≡ Δ
                     lem-03a = Γ₁ ⇃[ ι₀ ◆ (id ⇃⊔⇂ σ) ]⇂-Ctx  ⟨ Γ₁ ⇃[≀ reduce-ι₀ ≀]⇂-Ctx ⟩-≡
                               Γ₁ ⇃[ id ◆ ι₀ ]⇂-Ctx          ⟨ Γ₁ ⇃[≀ unit-l-◆ ≀]⇂-Ctx ⟩-≡
                               Γ₁ ⇃[ ι₀ ]⇂-Ctx               ∎-≡

                     -- lem-03b : ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘
                     --           ∼ ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ σ ◆ ι₁ ⦘
                     -- lem-03b = {!!}

                     map-lookup : ∀{Δ₀ Δ₁ : ℒHMCtx' k ξs} -> Δ₀ ≡ Δ₁
                                  -> lookup-DList Δ₀ k∍i .snd ⇃[ ⦗ id , ⟨ ι∀∍ Δ₀ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘ ]⇂
                                  ≡ lookup-DList Δ₁ k∍i .snd ⇃[ ⦗ id , ⟨ ι∀∍ Δ₁ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘ ]⇂
                     map-lookup = {!!}
-}
                     -- lem-03 : lookup-DList (Γ₁ ⇃[ ι₀ ◆ (id ⇃⊔⇂ σ) ]⇂-Ctx) k∍i .snd
                     --                       ⇃[ ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘ ]⇂
                     --          ≡
                     --          lookup-DList Δ k∍i .snd
                     --                       ⇃[ ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘ ]⇂
                     -- lem-03 = (λ i -> lookup-DList (lem-03a i) k∍i .snd
                     --                       ⇃[ ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ ι₁ ◆ (id ⇃⊔⇂ σ) ⦘ ]⇂ )

                              -- ⇃[ ⦗ id , ⟨ ι∀∍ Γ₁ k∍i ⟩ ◆ σ ◆ ι₁ ⦘ ]⇂

                     -- lem-01 : lookup-DList (Γ ⇃[ ρ ]⇂-Ctx) k∍i ≡ lookup-DList Γ k∍i ⇃[ ρ ]⇂-poly
                     -- lem-01 = {!!}

                     -- lem-08 : Γ₁ ⇃[ ι₀ ]⇂-Ctx ≡ Δ
                     -- lem-08 = refl-≡


                     lem-10 : α ⇃[ id ⇃⊔⇂ id ]⇂ ⇃[ tiσ ]⇂ ≡ δ
                     lem-10 = {!!}


                 in record { tiSub = tiσ ; typProof = lem-10 ; ctxProof = lem-20 ; subProof = {!!} }

               }

           )

{-
-}

γ Γ (slet te se) with γ Γ te
... | (left _) = {!!}
... | (right ((νs₀ ⊩ Γ₀ , τ₀ , Γ₀<Γ , Γ₀⊢τ₀), Ξ)) = {!!}
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
-- typecheck the first term with the given context
γ {μs = νs} Γ (app te se) = {!!}
{-
with γ Γ te
... | (left _) = {!!}
... | (right ((νs₀ ⊩ Γ₀ , α₀ , Γ<Γ₀ , Γ₀⊢α₀), Ω₀)) with γ Γ₀ se
... | (left _) = {!!}
... | (right ((νs₁ ⊩ Γ₁ , β₁ , Γ₀<Γ₁ , Γ₁⊢β₁), Ω₁)) = resn
  where

    σᵤ₀ : _ ⟶ νs₀
    σᵤ₀ = fst Γ<Γ₀

    -- lift the τ0 typing to Γ₁
    σ₀₁ : νs₀ ⟶ νs₁
    σ₀₁ = fst Γ₀<Γ₁

    -- we lift α₀ to the metas νs₁
    -- τ₀'
    α₁ : ℒHMType _
    α₁ = α₀ ⇃[ σ₀₁ ]⇂

    -- we need a new type variable for the return
    -- type of the application, so we move to νs₂
    νs₂ = (νs₁) ⊔ st
    σ₁₂ : νs₁ ⟶ νs₂
    σ₁₂ = ι₀

    -- τ₀''
    α₂ : ℒHMType ⟨ νs₂ ⟩
    α₂ = α₁ ⇃[ σ₁₂ ]⇂

    β₂ : ℒHMType ⟨ νs₂ ⟩
    β₂ = β₁ ⇃[ σ₁₂ ]⇂

    -- Γ₁'
    Γ₂ = Γ₁ ⇃[ σ₁₂ ]⇂-Ctx

    -- we call the new type γ
    γ₂ : ℒHMType ⟨ νs₂ ⟩
    γ₂ = var (right-∍ incl)

    -- the types which we unify are:
    u : ℒHMType ⟨ νs₂ ⟩
    u = α₂

    v : ℒHMType ⟨ νs₂ ⟩
    v = β₂ ⇒ γ₂

    res = unify-ℒHMTypes (asArr u) (asArr v)

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

{-
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
γ {μs} {k} Γ (lam te) = {!!}
{-
  let
    -- create a new metavariable
    μs' = μs ⊔ st

    -- create the context which contains this new variable
    Γ' : ℒHMCtx' (tt ∷ k) μs'
    Γ' = ∀[ (incl ◌) ] (var (left-∍ (right-∍ incl))) ∷ mapOf (ℒHMCtx' k) ι₀ Γ

    -- call typechecking recursively on `te`
    res = γ Γ' te

    -- distinguish between failure and not
  in case res of
      -- if there was a failure,
      -- we also have to fail
      (λ ¬typing → left
         -- assume we have a typing for lambda
         -- this means that we also have a typing for te
         -- which we know is impossible
         λ {(νs ⊩ Δ , τ , Γ'<Δ , hastyp)
                → let νs' , Δ' , τ' , hastyp' = §-isTypedℒHM.prop-1 te hastyp
                  in {!!} -- ¬typing (νs' ⊩ Δ' , τ' , {!!} , hastyp')
                  })


      -- if there was no failure, we can use this result
      λ {
        -- the case where our type suddenly has a quantification
        -- cannot occur
        ((νs ⊩ (∀[ incl (a ∷ as) ] α ∷ Δ) , β , Γ'<Δ , hastype) , Ξ) →
          {!!}

        -- we know that `α` has no quantification
        ; ((νs ⊩ (∀[] α ∷ Δ) , β , Γ'<Δ , hastype) , Ω) →

          right ((νs ⊩ Δ , _ , {!!} , lam hastype),

                -- here we have to show that we are the best typing instance
                λ {(ζs ⊩ Ξ , .(_ ⇒ _) , Γ<Ξ , lam {α = ξ₀} {β = ξ₁} Ξξ₀⊢ξ₁) →

                  let ΩR = Ω (ζs ⊩ (∀[] ξ₀) ∷ Ξ , ξ₁ , {!!} , Ξξ₀⊢ξ₁)

                      σ : νs ⟶ ζs
                      σ = tiSub ΩR

                      lem-1 : (∀[] α ∷ Δ) ⇃[ σ ]⇂-Ctx ≡ ∀[] ξ₀ ∷ Ξ
                      lem-1 = ctxProof ΩR

                      lem-2 : ((∀[] α) ⇃[ σ ]⇂-poly ≡ ∀[] ξ₀) × (Δ ⇃[ σ ]⇂-Ctx ≡ Ξ)
                      lem-2 = (λ i → split-DList (lem-1 i) .fst) , (λ i → split-DList (lem-1 i) .snd)

                      lem-3 : ∀[] α ⇃[ σ ⇃⊔⇂ id ]⇂ ≡ ∀[] ξ₀
                      lem-3 = lem-2 .fst

                      lem-4 : α ⇃[ σ ⇃⊔⇂ id ]⇂ ≡ ξ₀
                      lem-4 = isInjective:∀[] lem-3

                      lem-5 : α ⇃[ σ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ≡ ξ₀ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂
                      lem-5 = cong _⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ lem-4

                      lem-6 : α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ σ ]⇂ ≡ ξ₀ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂
                      lem-6 = α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ σ ]⇂          ⟨ functoriality-⇃[]⇂ {τ = α} {f = ⦗ id , elim-⊥ ⦘} {g = σ} ⟩-≡
                              α ⇃[ ⦗ id , elim-⊥ ⦘ ◆ σ ]⇂              ⟨ {!α ⇃[≀ ? ≀]⇂!} ⟩-≡
                              α ⇃[ (σ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘ ]⇂     ⟨ sym-Path (functoriality-⇃[]⇂ {τ = α} {f = σ ⇃⊔⇂ id} {g = ⦗ id , elim-⊥ ⦘}) ⟩-≡
                              α ⇃[ (σ ⇃⊔⇂ id) ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⟨ lem-5 ⟩-≡
                              ξ₀ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂                 ∎-≡

                      lem-9 : β ⇃[ σ ]⇂ ≡ ξ₁
                      lem-9 = typProof ΩR

                      lem-10 : (α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β) ⇃[ σ ]⇂ ≡ (ξ₀ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ ξ₁)
                      lem-10 = λ i → lem-6 i ⇒ lem-9 i

                  in record { tiSub = σ ; typProof = lem-10 ; ctxProof = lem-2 .snd }
                  })

        }
-}









{-
γ Γ (app te se) =
  -- typecheck the first term with the given context
  case γ Γ te of
    {!!}
    λ {(νs₀ ⊩ Γ₀ , τ₀ , Γ₀<Γ , Γ₀⊢τ₀ ) ->

        -- typecheck the second term with the returned context
        case γ Γ₀ se of
          {!!}
          λ {(νs₁ ⊩ Γ₁ , τ₁ , Γ₁<Γ₀ , Γ₁⊢τ₁ ) ->
            -- lift the τ0 typing to Γ₁
            let σᵤ₀ : νs₀ ⟶ νs₁
                σᵤ₀ = fst Γ₁<Γ₀

                -- we lift the old type τ₀ to the metas νs₁
                τ₀' : ℒHMType _
                τ₀' = τ₀ ⇃[ σᵤ₀ ⇃⊔⇂ id ]⇂

                -- we need a new type variable for the return
                -- type of the application, so we move to νs₂
                νs₂ = (νs₁ ⊔ ⊥) ⊔ st

                τ₀'' : ℒHMType ⟨ νs₂ ⟩
                τ₀'' = τ₀' ⇃[ ι₀ ]⇂

                -- we call the new type β
                β : ℒHMType ⟨ νs₂ ⟩
                β = var (right-∍ incl)

                -- the types which we unify are:
                ϕ : ℒHMType ⟨ νs₂ ⟩
                ϕ = τ₀'' ⇒ β

                ψ : ℒHMType ⟨ νs₂ ⟩
                ψ = τ₁ ⇃[ ι₀ ]⇂

                res : (¬ hasCoequalizerCandidate (asArr ϕ , asArr ψ)) + (hasCoequalizer (asArr ϕ) (asArr ψ))
                res = unify (asArr ϕ) (asArr ψ)

                -- typing₀ : isTypedℒHM (Γ₁ ⊢ )
                -- typing₀ = ?

            in case res of
                {!!}
                λ {x → {!!}
                }

                -- case res of
                -- ωs : ℒHMTypes
                -- ωs = {!!}

                -- ρ : ℒHMType ⟨ ωs ⟩
                -- ρ = {!!}
            }
      }

-}
