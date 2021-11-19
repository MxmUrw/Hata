
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

{-

record 人Vecᵖ (A : 𝒰 𝑖) (n : 人ℕ) : 𝒰 𝑖 where
  constructor vecᵖ
  field ⟨_⟩ : 人List A
  field hasSize : map-Free-𝐌𝐨𝐧 (const tt) ⟨_⟩ ≡ n

open 人Vecᵖ public

get-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (n ∍ i) -> A
get-人Vecᵖ = {!!}

get-∍-人Vecᵖ : ∀{i} -> ∀{A : 𝒰 𝑖} {n : 人ℕ} -> (xs : 人Vecᵖ A n) -> (p : n ∍ i) -> ⟨ xs ⟩ ∍ get-人Vecᵖ xs p
get-∍-人Vecᵖ = {!!}

-}

module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-D人List : ∀{m} -> D人List F m -> 人List A
  size-D人List {m} _ = m

module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-DList : ∀{m} -> DList F m -> List A
  size-DList {m} _ = m

module _ (n : ♮ℕ) (m : ℒHMTypes) where
  ℒHMCtx'ᵘ = DList (const (ℒHMPolyType m)) n

module _ (n : ♮ℕ) where
  macro ℒHMCtx' = #structureOn (ℒHMCtx'ᵘ n)

map-ℒHMCtx' : ∀{n : ♮ℕ} -> {a b : ℒHMTypes} -> a ⟶ b -> ℒHMCtx' n a ⟶ ℒHMCtx' n b
map-ℒHMCtx' f [] = []
map-ℒHMCtx' f (b ∷ x) = (mapOf ℒHMPolyType f b) ∷ map-ℒHMCtx' f x

instance
  isFunctor:ℒHMCtx'  : ∀{n} -> isFunctor ℒHMTypes 𝐔𝐧𝐢𝐯₀ (ℒHMCtx' n)
  isFunctor.map isFunctor:ℒHMCtx' = map-ℒHMCtx'
  isFunctor.isSetoidHom:map isFunctor:ℒHMCtx' = {!!}
  isFunctor.functoriality-id isFunctor:ℒHMCtx' = {!!}
  isFunctor.functoriality-◆ isFunctor:ℒHMCtx' = {!!}


record ℒHMJudgementᵈ : 𝒰₀ where
  constructor _⊩_⊢_
  field metavars : ℒHMTypes
  field {contextsize} : ♮ℕ
  field context : DList (const (ℒHMPolyType metavars)) contextsize
  -- ℒHMCtx' metavars
  field type : ℒHMPolyType metavars

open ℒHMJudgementᵈ public

macro ℒHMJudgement = #structureOn ℒHMJudgementᵈ

instance
  isCategory:ℒHMJudgement : isCategory {ℓ₀ , ℓ₀} ℒHMJudgement
  isCategory:ℒHMJudgement = {!!}


ℒHMJudgementCategory : 𝐂𝐚𝐭₀
ℒHMJudgementCategory = ℒHMJudgement

pattern _∷'_ x xs = _∷_ {a = tt} x xs
infix 30 ∀[]_
pattern ∀[]_ xs = ∀[ incl [] ] xs

data isAbstr (m : ℒHMTypes) : (a b : ℒHMJudgement) -> 𝒰₀ where
  -- incl : ∀{k n} -> ∀{τ : ℒHMPolyType (n ⊔ m)} -> ∀{Γ : ℒHMCtx' n k}
  --        -> isAbstr m (mapOf ℒHMCtx' ι₀ μs ⊩ Γ ⊢ τ) (μs ⊩ Γ ⊢ abstr τ)

data TypedℒHMᵈ (X : ℒHMJudgement -> 𝒰₀) : (Γ : ℒHMJudgement) -> 𝒰₀ where
  var  : ∀{μs k} -> {Γ : ℒHMCtx' k μs} {α : ℒHMPolyType μs}
         -- -> Γ ∍ α
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ α)

  hole : ∀{Γ} -> X Γ -> TypedℒHMᵈ X Γ

  gen : ∀{m a b} -> isAbstr m a b -> TypedℒHMᵈ X a -> TypedℒHMᵈ X b

  app : ∀{μs k} {Γ : ℒHMCtx' k μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] (α ⇒ β))
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] α)
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] β)

  lam : ∀{μs k} {Γ : ℒHMCtx' k μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X (μs ⊩ ((∀[] α) ∷' Γ) ⊢ ∀[] β)
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[] α ⇒ β)

  lam2 : ∀{μs k vβ} {Γ : ℒHMCtx' k μs}
         {α : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
         {β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ι vβ ⟩ tt}
         -> TypedℒHMᵈ X (μs ⊩ ((∀[] α) ∷' Γ) ⊢ ∀[ vβ ] β)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ vβ ] (α ⇃[ id {a = μs} ⇃⊔⇂ elim-⊥ ]⇂) ⇒ β)

  -- convert : ∀{m0 m1 k} -> (m0 ⟶ m1) -> {Γ₀ : ℒHMCtx' k m0} -> ∀{τ₀} -> {Γ₁ : ℒHMCtx' k m1} -> ∀{τ₁}
  --           -> TypedℒHMᵈ X (m0 ⊩ Γ₀ ⊢ τ₀)
  --           -> TypedℒHMᵈ X (m1 ⊩ Γ₁ ⊢ τ₁)

  mapmeta : ∀{k μs νs} (ϕ : μs ⟶ νs) -> {Γ₀ : ℒHMCtx' k μs} -> ∀{τ₀}
            -> TypedℒHMᵈ X (μs ⊩ Γ₀ ⊢ τ₀)
            -> TypedℒHMᵈ X (νs ⊩ mapOf (ℒHMCtx' k) ϕ Γ₀ ⊢ mapOf ℒHMPolyType ϕ τ₀)

  instantiate : ∀{μs k} {Γ : ℒHMCtx' k μs} {α β : ℒHMPolyType μs}
         -> (α ⟶ β)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ α)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ β)

instance
  isCategory:TypedℒHM : ∀{X Γ} -> isCategory {ℓ₀ , ℓ₀} (TypedℒHMᵈ X Γ)
  isCategory:TypedℒHM = {!!}


{-

record ℒHMJudgement : 𝒰₀ where
  constructor _⊢_
  field {metavars} : ℒHMTypes
  field context : ℒHMCtx metavars
  field type : ℒHMPolyType metavars

open ℒHMJudgement public

data isAbstr (m : ℒHMTypes) : (a b : ℒHMJudgement) -> 𝒰₀ where
  incl : ∀{n} -> ∀{τ : ℒHMPolyType (n ⊔ m)} -> ∀{Γ : ℒHMCtx n}
         -> isAbstr m (mapOf ℒHMCtx ι₀ μs ⊩ Γ ⊢ τ) (μs ⊩ Γ ⊢ abstr τ)

data TypedℒHMᵈ (X : ℒHMJudgement -> 𝒰₀) : (Γ : ℒHMJudgement) -> 𝒰₀ where
  var  : ∀{μs} -> {Γ : ℒHMCtx μs} {α : ℒHMPolyType μs}
         -> Γ ∍ α -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ α)

  hole : ∀{Γ} -> X Γ -> TypedℒHMᵈ X Γ

  gen : ∀{m a b} -> isAbstr m a b -> TypedℒHMᵈ X a -> TypedℒHMᵈ X b

  app : ∀{μs} {Γ : ℒHMCtx μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] (α ⇒ β))
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] α)
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] β)

  lam : ∀{μs} {Γ : ℒHMCtx μs} {α β : Term₁-𝕋× 𝒹 ⟨ μs ⊔ ⊥ ⟩ tt}
        -> TypedℒHMᵈ X ((Γ ⋆ incl (∀[ ⊥ ] α)) ⊢ ∀[ ⊥ ] β)
        -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ ∀[ ⊥ ] α ⇒ β)

  convert : ∀{m0 m1} -> (m0 ⟶ m1) -> {Γ₀ : ℒHMCtx m0} -> ∀{τ₀} -> {Γ₁ : ℒHMCtx m1} -> ∀{τ₁}
            -> TypedℒHMᵈ X (Γ₀ ⊢ τ₀)
            -> TypedℒHMᵈ X (Γ₁ ⊢ τ₁)

  instantiate : ∀{μs} {Γ : ℒHMCtx μs} {α β : ℒHMPolyType μs}
         -> (α ⟶ β)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ α)
         -> TypedℒHMᵈ X (μs ⊩ Γ ⊢ β)

-}

TypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
TypedℒHMᵘ A = indexed (TypedℒHMᵈ (ix A))

macro TypedℒHM = #structureOn TypedℒHMᵘ



-- module mytest where
--   Γ : ℒHMCtx ⊥
--   Γ = ◌

  -- mytest : TypedℒHMᵈ (const ⊥-𝒰) (μs ⊩ Γ ⊢ ∀[ incl (incl tyᵗ) ] var (right-∍ incl) ⇒ var (right-∍ incl))
  -- mytest = convert id (gen incl (lam (var (right-∍ incl))))


-- TypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
-- TypedℒHMᵘ A = indexed (TypedℒHMᵈ (ix A))

-- macro TypedℒHM = #structureOn TypedℒHMᵘ


