
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Definition where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Definition

-----------------------------------------
-- 人Vecᵖ

record 人Vecᵖ (A : 𝒰 𝑖) (n : 人ℕ) : 𝒰 𝑖 where
  constructor vecᵖ
  field ⟨_⟩ : ⋆List A
  field hasSize : map-⋆List (const tt) ⟨_⟩ ≡ n

open 人Vecᵖ public

get-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (n ∍ i) -> A
get-人Vecᵖ = {!!}

get-∍-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (p : n ∍ i) -> ⟨ xs ⟩ ∍ get-人Vecᵖ xs p
get-∍-人Vecᵖ = {!!}




module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-⋆Listᴰ : ∀{m} -> ⋆Listᴰ F m -> ⋆List A
  size-⋆Listᴰ {m} _ = m

module _ (m : ℒHMTypes) (n : 人ℕ) where
  ℒHMCtx' = ⋆Listᴰ (const (ℒHMPolyType m)) n

record ℒHMJudgementᵈ : 𝒰₀ where
  constructor _⊢_
  field {metavars} : ℒHMTypes
  field {contextsize} : 人ℕ
  field context : ⋆Listᴰ (const (ℒHMPolyType metavars)) contextsize
  -- ℒHMCtx' metavars
  field type : ℒHMPolyType metavars

open ℒHMJudgementᵈ public

macro ℒHMJudgement = #structureOn ℒHMJudgementᵈ

instance
  isCategory:ℒHMJudgement : isCategory {ℓ₀ , ℓ₀} ℒHMJudgement
  isCategory:ℒHMJudgement = {!!}


ℒHMJudgementCategory : 𝐂𝐚𝐭₀
ℒHMJudgementCategory = ℒHMJudgement


data isAbstr (m : ℒHMTypes) : (a b : ℒHMJudgement) -> 𝒰₀ where
  -- incl : ∀{k n} -> ∀{τ : ℒHMPolyType (n ⊔ m)} -> ∀{Γ : ℒHMCtx' n k}
  --        -> isAbstr m (mapOf ℒHMCtx' ι₀ Γ ⊢ τ) (Γ ⊢ abstr τ)

data TypedℒHMᵈ (X : ℒHMJudgement -> 𝒰₀) : (Γ : ℒHMJudgement) -> 𝒰₀ where
  var  : ∀{metas k} -> {Γ : ℒHMCtx' metas k} {α : ℒHMPolyType metas}
         -- -> Γ ∍ α
         -> TypedℒHMᵈ X (Γ ⊢ α)

  hole : ∀{Γ} -> X Γ -> TypedℒHMᵈ X Γ

  gen : ∀{m a b} -> isAbstr m a b -> TypedℒHMᵈ X a -> TypedℒHMᵈ X b

  app : ∀{metas k} {Γ : ℒHMCtx' metas k} {α β : Term₁-𝕋× 𝒹 ⟨ metas ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X (Γ ⊢ ∀[ ⊥ ] (α ⇒ β))
        -> TypedℒHMᵈ X (Γ ⊢ ∀[ ⊥ ] α)
        -> TypedℒHMᵈ X (Γ ⊢ ∀[ ⊥ ] β)

  lam : ∀{metas k} {Γ : ℒHMCtx' metas k} {α β : Term₁-𝕋× 𝒹 ⟨ metas ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X ((Γ ⋆-⧜ (incl {a = tt} (∀[ ⊥ ] α))) ⊢ ∀[ ⊥ ] β)
        -> TypedℒHMᵈ X (Γ ⊢ ∀[ ⊥ ] α ⇒ β)

  convert : ∀{m0 m1 k} -> (m0 ⟶ m1) -> {Γ₀ : ℒHMCtx' m0 k} -> ∀{τ₀} -> {Γ₁ : ℒHMCtx' m1 k} -> ∀{τ₁}
            -> TypedℒHMᵈ X (Γ₀ ⊢ τ₀)
            -> TypedℒHMᵈ X (Γ₁ ⊢ τ₁)

  instantiate : ∀{metas k} {Γ : ℒHMCtx' metas k} {α β : ℒHMPolyType metas}
         -> (α ⟶ β)
         -> TypedℒHMᵈ X (Γ ⊢ α)
         -> TypedℒHMᵈ X (Γ ⊢ β)

instance
  isCategory:TypedℒHM : ∀{X Γ} -> isCategory {ℓ₀ , ℓ₀} (TypedℒHMᵈ X Γ)
  isCategory:TypedℒHM = {!!}

-- instance
--   isCategory:人ℕ : isCategory {ℓ₀ , ℓ₀} 人ℕ
--   isCategory:人ℕ = {!!}



TypedℒHMᵘ : 𝐅𝐮𝐧𝐜 ℒHMJudgement (𝐂𝐚𝐭 (ℓ₀ , ℓ₀ , ℓ₀)) -> 𝐅𝐮𝐧𝐜 (ℒHMJudgement) (𝐂𝐚𝐭 _)
TypedℒHMᵘ X = (λ Γ → ′ TypedℒHMᵈ (λ a -> ⟨ ⟨ X ⟩ a ⟩) Γ ′) since {!!}




-- {!λ Γ -> ′ TypedℒHMᵈ ⟨ X ⟩ Γ ′ since ?!}

-- indexed (TypedℒHMᵈ (ix A))

-- TypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)

macro TypedℒHM = #structureOn TypedℒHMᵘ






