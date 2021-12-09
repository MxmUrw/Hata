
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.Infer where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.Monad

open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Instance.Monad


forgetJudgement : 𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀ -> 𝐈𝐱 人ℕ 𝐔𝐧𝐢𝐯₀
forgetJudgement x = indexed (λ n →  ∑ λ metas -> ∑ λ (Γ : 人Vecᵖ (ℒHMPolyType metas) n) -> ∑ λ (τ : ℒHMPolyType metas) -> x ⌄ (⟨ Γ ⟩ ⊢ τ))

-- ∑ λ (j : ℒHMJudgement) -> (mapOf ′ ⋆List ′ (const tt) (context j) ≣ i) × (x ⌄ j))

instance
  isFunctor:forgetJudgement : isFunctor (𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀) (𝐈𝐱 人ℕ 𝐔𝐧𝐢𝐯₀) forgetJudgement
  isFunctor:forgetJudgement = {!!}

{-
{-# TERMINATING #-}
printᵘ-TypedℒHM : ∀ A -> forgetJudgement (TypedℒHM A) ⟶ UntypedℒHM (forgetJudgement A)
printᵘ-TypedℒHM A Γ (.(_ ⊢ _) , refl-≣ , var x) = var (map-∍ (const tt) x)
printᵘ-TypedℒHM A Γ (j , refl-≣ , hole x) = hole (j , refl-≣ , x)
printᵘ-TypedℒHM A Γ (j , refl-≣ , gen x te) = printᵘ-TypedℒHM A Γ (_ , {!!} , te)
printᵘ-TypedℒHM A Γ (.(_ ⊢ (∀[ _ ] _)) , refl-≣ , app te te₁) = {!!}
printᵘ-TypedℒHM A Γ (.(_ ⊢ (∀[ _ ] _ ⇒ _)) , refl-≣ , lam te) = {!!}
printᵘ-TypedℒHM A Γ (.(_ ⊢ _) , refl-≣ , convert x te) = {!!}
printᵘ-TypedℒHM A Γ (.(_ ⊢ _) , refl-≣ , instantiate x te) = {!!}

print-TypedℒHM : 大MonadHom (_ , TypedℒHM) (_ , UntypedℒHM)
print-TypedℒHM = record { fst = ′ forgetJudgement ′ ; snd = printᵘ-TypedℒHM since {!!} }

-}

makeJudgement : 𝐈𝐱 人ℕ 𝐔𝐧𝐢𝐯₀ -> 𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀
makeJudgement = 写* (λ (Γ ⊢ τ) → map-⋆List (const tt) Γ)

-- map-⋆List (const tt)
-- indexed (λ (Γ ⊢ τ) → x ⌄ map-⋆List (const tt) Γ)

print2-TypedℒHM : ∀ A -> TypedℒHM (makeJudgement A) ⟶ makeJudgement (UntypedℒHM A)
print2-TypedℒHM A (Γ ⊢ τ) (var x) = var (map-∍ (const tt) x)
print2-TypedℒHM A (Γ ⊢ τ) (hole x) = hole x
print2-TypedℒHM A (Γ ⊢ τ) (gen x te) = {!!}
print2-TypedℒHM A (Γ ⊢ (∀[ _ ] snd₁)) (app x y) = app (print2-TypedℒHM _ _ x) (print2-TypedℒHM _ _ y)
print2-TypedℒHM A (Γ ⊢ (∀[ _ ] .(_ ⇒ _))) (lam x) = lam (print2-TypedℒHM _ _ x)
print2-TypedℒHM A (Γ ⊢ τ) (convert x x₁) = {!!}
print2-TypedℒHM A (Γ ⊢ τ) (instantiate x te) = print2-TypedℒHM _ _ te


-- this is the type inference for ℒHM
module ℒHM-Inference where
  private
    -- ℒHMFin


    f : ∀ {A} metas n
        -> (Γ : 人Vecᵖ (ℒHMPolyType metas) n)
        -> UntypedℒHM A ⌄ n
        -> ∑ λ τ -> TypedℒHM (makeJudgement (UntypedℒHM A)) ⌄ (⟨ Γ ⟩ ⊢ τ)
    f {A} metas n Γ (var x) = _ , var (get-∍-人Vecᵖ Γ x)
    f {A} metas n Γ (hole x) = {!!} , (hole (hole {!!}))
    f {A} metas n Γ (slet te te₁) = {!!}
    f {A} metas n Γ (app te te₁) = {!!}
    f {A} metas n Γ (lam te) =
      let
          -- we create a new type variable
          -- by increasing the metas
          metas₁ = metas ⊔ st

          -- we embed the old context into
          -- the one containing the new variable
          Γ' = mapOf ℒHMCtx ι₀ ⟨ Γ ⟩

          -- the new context contains the new type variable
          Γ₁ = Γ' ⋆ incl (∀[ ⊥ ] (var (left-∍ (right-∍ incl))))

          -- we infer the type of the body of the lambda expression
          β , te' = f metas₁ _ (vecᵖ Γ₁ {!!}) te

      in {!!}


infer-TypedℒHM : ∀ A -> UntypedℒHM A ⟶ forgetJudgement (TypedℒHM (makeJudgement (UntypedℒHM A)))
infer-TypedℒHM A x te = {!!} , {!!} , {!!} , {!!}






