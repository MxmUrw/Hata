
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition where

open import Verification.Experimental.Conventions hiding (isSet)
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition as SingleSorted
open import Verification.Experimental.Theory.Std.TypeTheory.Definition

data TySig : ℕ -> 𝒰₀ where
  `ℕ` `𝔹` : TySig 0
  `⇒` : TySig 2


-- Defining types

Ty-λ : 𝒰₀ -> 𝒰₀
Ty-λ = SingleSorted.Term TySig

infixr 50 _⇒_
pattern _⇒_ σ τ = te `⇒` (σ ∷ τ ∷ [])



data Term-λ : ℕ -> 𝒰₀ where
  app : (f g : Term-λ n) -> Term-λ n
  lam : (t : Term-λ (suc n)) -> Term-λ n
  var : 𝔽ʳ n -> Term-λ n
  zero : Term-λ n
  suc : Term-λ n -> Term-λ n
  rec-ℕ : Term-λ (suc n) -> Term-λ n -> Term-λ n -> Term-λ n

-- data SCtx (A : 𝒰₀) : 𝒰₀ where
--   [] : SCtx A
--   _,_ : SCtx A -> Ty-λ A -> SCtx A

instance
  IBootEq:⊥ : ∀{𝑖} -> IBootEq {𝑖} (⊥)
  IBootEq:⊥ = {!!}

-- instance
--   IBootEq:SCtx : ∀{A} -> {{_ : IBootEq A}} -> IBootEq (SCtx A)
--   IBootEq:SCtx = {!!}

instance
  IBootEq:TySig : IBootEq (TySig n)
  IBootEq:TySig = {!!}

instance
  IBootEq:Term : ∀{A σ} -> {{_ : IBootEq A}} -> {{∀ {n} -> IBootEq (σ n)}} -> IBootEq (SingleSorted.Term {𝑖} σ A)
  IBootEq:Term = {!!}

Info : 𝒰₀
Info = Judgement (SCtx ⊥) (Ty-λ ⊥)

Statement : 𝒰₀
Statement = ∑ λ n -> Judgement (SCtx (Fin n)) (Ty-λ (Fin n))

instance
  isSet:Statement : isSet Statement
  isSet:Statement = record { fillPath-Set = {!!} }

-- instance
--   isSetoid:Term : isSetoid _ Term-λ
--   isSetoid:Term = setoid _≣_

-- data πVar : ∀{A} -> ℕ -> SCtx A -> Ty-λ A -> 𝒰₁ where
--   zero : ∀{A} -> ∀{Γ : SCtx A} -> {τ : Ty-λ A} -> πVar 0 (Γ , τ) τ
--   suc : ∀{A n} -> ∀{Γ : SCtx A} -> {σ τ : Ty-λ A} -> πVar n Γ σ -> πVar (suc n) (Γ , τ) σ

-- data _∶_⊢_ : ∀{A} -> Term-λ -> SCtx A -> Ty-λ A -> 𝒰₁ where
--   var : ∀{A n} -> ∀{Γ : SCtx A} {τ : Ty-λ A} -> πVar n Γ τ -> (var n) ∶ Γ ⊢ τ
--   app : ∀{A} -> ∀{t s} -> ∀{Γ : SCtx A} {τ σ : Ty-λ A} -> (t ∶ Γ ⊢ σ ⇒ τ) -> (s ∶ Γ ⊢ σ) -> (app s t ∶ Γ ⊢ τ)
--   lam : ∀{A} -> ∀{t} -> ∀{Γ : SCtx A} {τ σ : Ty-λ A} -> (t ∶ (Γ , σ) ⊢ τ) -> (lam t ∶ Γ ⊢ σ ⇒ τ)




