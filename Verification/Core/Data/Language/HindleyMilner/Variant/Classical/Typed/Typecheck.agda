
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Category.Std.AllOf.Collection.Monads
-- open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition

open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Set.Decidable



record _<Γ_ {k} {μs νs} (Γ : ℒHMCtx' k μs) (Γ' : ℒHMCtx' k νs) : 𝒰₀ where
  field fst : μs ⟶ νs
  -- field snd 
open _<Γ_ public

record CtxTypingInstance {μs k} (Γ : ℒHMCtx' k μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _⊩_,_,_,_
  field metas : ℒHMTypes
  field ctx : ℒHMCtx' k metas
  field typ : ℒHMType (⟨ metas ⟩)
  field isInstance : Γ <Γ ctx
  field hasType : isTypedℒHM (metas ⊩ ctx ⊢ typ) te

open CtxTypingInstance public

γ : ∀{μs k} -> (Γ : ℒHMCtx' k μs) -> (te : UntypedℒHM k)
  -> (CtxTypingInstance Γ te -> ⊥-𝒰 {ℓ₀})
    +
     CtxTypingInstance Γ te
γ Γ var = {!!}
γ Γ (slet te se) with γ Γ te
... | (left _) = {!!}
... | (right (νs₀ ⊩ Γ₀ , τ₀ , Γ₀<Γ , Γ₀⊢τ₀)) =
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

-- the case of an application
-- typecheck the first term with the given context
γ Γ (app te se) = {!!}
{-
 with γ Γ te
... | (left _) = {!!}
... | (right (νs₀ ⊩ Γ₀ , τ₀ , Γ₀<Γ , Γ₀⊢τ₀ )) with γ Γ₀ se
... | (left _) = {!!}
... | (right (νs₁ ⊩ Γ₁ , τ₁ , Γ₁<Γ₀ , Γ₁⊢τ₁ )) = resn
  where
    -- lift the τ0 typing to Γ₁
    σ₀ : νs₀ ⟶ νs₁
    σ₀ = fst Γ₁<Γ₀

    -- we lift the old type τ₀ to the metas νs₁
    τ₀' : ℒHMType _
    τ₀' = τ₀ ⇃[ σ₀ ]⇂

    -- we need a new type variable for the return
    -- type of the application, so we move to νs₂
    νs₂ = (νs₁) ⊔ st

    τ₀'' : ℒHMType ⟨ νs₂ ⟩
    τ₀'' = τ₀' ⇃[ ι₀ ]⇂

    -- we call the new type β
    β : ℒHMType ⟨ νs₂ ⟩
    β = var (right-∍ incl)

    -- the types which we unify are:
    ϕ : ℒHMType ⟨ νs₂ ⟩
    ϕ = τ₀''

    τ₁' : ℒHMType ⟨ νs₂ ⟩
    τ₁' = τ₁ ⇃[ ι₀ ]⇂ ⇒ β

    Γ₁' : ℒHMCtx' _ νs₂
    Γ₁' = Γ₁ ⇃[ ι₀ ]⇂-Ctx

    res = unify-ℒHMTypes (asArr ϕ) (asArr τ₁')

    resn = case res of
           {!!}
           λ x →
             let σ = π₌
                 β₂ = β ⇃[ σ ]⇂
                 Γ₂ = Γ₁' ⇃[ σ ]⇂-Ctx

                 -- move the typing of se to Γ₂ = Γ₁[ ι₀ ◆ σ ]
                 sp : isTypedℒHM (νs₂ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx) ⊢ (τ₁ ⇃[ ι₀ ]⇂)) se
                 sp = §-isTypedℒHM.prop-2 ι₀ Γ₁⊢τ₁

                 sp' : isTypedℒHM (⟨ x ⟩ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx ⇃[ σ ]⇂-Ctx) ⊢ (τ₁ ⇃[ ι₀ ]⇂ ⇃[ σ ]⇂)) se
                 sp' = §-isTypedℒHM.prop-2 σ sp

                 -- move the typing of te to Γ₂ = Γ₀[ σ₀ ◆ ι₀ ◆ σ ]
                 tp : isTypedℒHM (νs₁ ⊩ Γ₁ ⊢ (τ₀ ⇃[ σ₀ ]⇂)) te
                 tp = {!!}

                 tp' : isTypedℒHM (νs₂ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx) ⊢ (τ₀ ⇃[ σ₀ ]⇂ ⇃[ ι₀ ]⇂)) te
                 tp' = §-isTypedℒHM.prop-2 ι₀ tp

                 tp'' : isTypedℒHM (⟨ x ⟩ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx ⇃[ σ ]⇂-Ctx) ⊢ (τ₀ ⇃[ σ₀ ]⇂ ⇃[ ι₀ ]⇂ ⇃[ σ ]⇂)) te
                 tp'' = §-isTypedℒHM.prop-2 σ tp'

                 tp''' : isTypedℒHM (⟨ x ⟩ ⊩ (Γ₁ ⇃[ ι₀ ]⇂-Ctx ⇃[ σ ]⇂-Ctx) ⊢ (τ₁ ⇃[ ι₀ ]⇂ ⇃[ σ ]⇂ ⇒ β ⇃[ σ ]⇂)) te
                 tp''' = {!!}

             in right (⟨ x ⟩ ⊩ Γ₂ , β₂ , {!!} , app tp'''  sp')
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
        -- we know that `α` has no quantification
        (νs ⊩ (∀[] α ∷ Δ) , β , Γ'<Δ , hastype) →

          right (νs ⊩ Δ , _ , {!!} , lam2 hastype)

        -- the case where our type suddenly has a quantification
        -- cannot occur
        ;(νs ⊩ (∀[ incl (a ∷ as) ] α ∷ Δ) , β , Γ'<Δ , hastype) →
          {!!}
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
            let σ₀ : νs₀ ⟶ νs₁
                σ₀ = fst Γ₁<Γ₀

                -- we lift the old type τ₀ to the metas νs₁
                τ₀' : ℒHMType _
                τ₀' = τ₀ ⇃[ σ₀ ⇃⊔⇂ id ]⇂

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
