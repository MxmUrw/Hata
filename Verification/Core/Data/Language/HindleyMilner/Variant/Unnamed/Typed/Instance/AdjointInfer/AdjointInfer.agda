
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.AdjointInfer where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.Monad

open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Instance.Monad



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑖} (f : Functor 𝒞 𝒟) where
  ∆* : 𝐅𝐮𝐧𝐜 𝒟 (𝐂𝐚𝐭 𝑖) -> 𝐅𝐮𝐧𝐜 𝒞 (𝐂𝐚𝐭 𝑖)
  ∆* g = f ◆-𝐂𝐚𝐭 g

  ₗ∆ : 𝐅𝐮𝐧𝐜 𝒞 (𝐂𝐚𝐭 𝑖) -> 𝐅𝐮𝐧𝐜 𝒟 (𝐂𝐚𝐭 𝑖)
  ₗ∆ g = h since {!!}
    where
      h : ⟨ 𝒟 ⟩ -> 𝐂𝐚𝐭 𝑖
      h d = ⨊ (F ◆-𝐂𝐚𝐭 g)
        where
          𝒞'ᵘ : 𝒰 _
          𝒞'ᵘ = ∑ λ (c : ⟨ 𝒞 ⟩) -> ⟨ f ⟩ c ≣ d

          Fᵘ : 𝒞'ᵘ -> ⟨ 𝒞 ⟩
          Fᵘ = fst

          𝒞' : 𝐂𝐚𝐭 _
          𝒞' = 𝒞'ᵘ since {!!}

          F : 𝒞' ⟶ 𝒞
          F = Fᵘ since {!!}




sᵘ : ℒHMJudgement -> 人ℕ
sᵘ (Γ ⊢ τ) = size-D人List Γ
-- map-Free-𝐌𝐨𝐧 (const tt) Γ

macro s = #structureOn sᵘ

instance
  isFunctor:s : isFunctor ℒHMJudgement 人ℕ s
  isFunctor:s = {!!}

ま : 𝐅𝐮𝐧𝐜 人ℕ 𝐂𝐚𝐭₀ -> 𝐅𝐮𝐧𝐜 ℒHMJudgement 𝐂𝐚𝐭₀
ま = ∆* s

ふ : 𝐅𝐮𝐧𝐜 ℒHMJudgement 𝐂𝐚𝐭₀ -> 𝐅𝐮𝐧𝐜 人ℕ 𝐂𝐚𝐭₀
ふ = ₗ∆ s

-- 写* (λ (Γ ⊢ τ) → map-Free-𝐌𝐨𝐧 (const tt) Γ)


π : ∀ A -> TypedℒHM (ま A) ⟶ ま (UntypedℒHM A)
π A = πᵘ since {!!}
  where
    πᵘᵘ : ∀ x -> ⟨ ⟨ (TypedℒHM (ま A)) ⟩ x ⟩ -> ⟨ ⟨ (ま (UntypedℒHM A)) ⟩ x ⟩
    πᵘᵘ .(_ ⊢ _) (var) = {!!} -- var (map-∍ (const tt) x)
    πᵘᵘ x (hole x₁) = hole x₁
    πᵘᵘ x (gen x₁ te) = {!!}
    πᵘᵘ .(_ ⊢ (∀[ _ ] _)) (app te te₁) = {!!}
    πᵘᵘ .(_ ⊢ (∀[ _ ] _ ⇒ _)) (lam te) = {!!}
    πᵘᵘ .(_ ⊢ _) (convert x te) = {!!}
    πᵘᵘ .(_ ⊢ _) (instantiate x te) = {!!}

    πᵘ : ∀ x -> ⟨ (TypedℒHM (ま A)) ⟩ x ⟶ ⟨ (ま (UntypedℒHM A)) ⟩ x
    πᵘ = λ x -> πᵘᵘ x since {!!}


γ : ∀ A -> UntypedℒHM A ⟶ ふ (TypedℒHM (ま (UntypedℒHM A)))
γ A = γᵘ since {!!}
  where
    γᵘᵘ : ∀ x -> ⟨ ⟨ UntypedℒHM A ⟩ x ⟩ -> ⟨ ⟨ ふ (TypedℒHM (ま (UntypedℒHM A))) ⟩ x ⟩
    γᵘᵘ x (var x₁) = {!!}
    γᵘᵘ x (hole x₁) = {!!}
    γᵘᵘ x (slet te te₁) = {!!}
    γᵘᵘ x (app te te₁) = {!!}
    γᵘᵘ x (lam te) with γᵘᵘ {!!} te
    ... | (((Γ ⋆-⧜ incl x₁) ⊢ (∀[ fst₁ ] snd₁)) , refl-≣) , tx = (Γ ⊢ {!!} , refl-≣) , {!!}

    γᵘ : ∀ x -> ⟨ UntypedℒHM A ⟩ x ⟶ ⟨ ふ (TypedℒHM (ま (UntypedℒHM A))) ⟩ x
    γᵘ = λ x -> γᵘᵘ x since {!!}




{-
forgetJudgement : 𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀ -> 𝐈𝐱 人ℕ 𝐔𝐧𝐢𝐯₀
forgetJudgement x = indexed (λ n →  ∑ λ metas -> ∑ λ (Γ : 人Vecᵖ (ℒHMPolyType metas) n) -> ∑ λ (τ : ℒHMPolyType metas) -> x ⌄ (⟨ Γ ⟩ ⊢ τ))

-- ∑ λ (j : ℒHMJudgement) -> (mapOf ′ Free-𝐌𝐨𝐧 ′ (const tt) (context j) ≣ i) × (x ⌄ j))

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
makeJudgement = 写* (λ (Γ ⊢ τ) → map-Free-𝐌𝐨𝐧 (const tt) Γ)

-- map-Free-𝐌𝐨𝐧 (const tt)
-- indexed (λ (Γ ⊢ τ) → x ⌄ map-Free-𝐌𝐨𝐧 (const tt) Γ)

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



-}


