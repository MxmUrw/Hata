
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition where

open import Verification.Experimental.Conventions hiding (isSet)
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition

data TySig : ℕ -> 𝒰₀ where
  `ℕ` `𝔹` : TySig 0
  `⇒` : TySig 2


-- Defining types

Ty-λ : 𝒰₀ -> 𝒰₀
Ty-λ = Term TySig

infixr 50 _⇒_
pattern _⇒_ σ τ = te `⇒` (σ ∷ τ ∷ [])

record Judgement (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _⊢_
  field fst : A
  field snd : B

open Judgement public


data Term-λ : 𝒰₀ where
  app : (f g : Term-λ) -> Term-λ
  lam : (t : Term-λ) -> Term-λ
  var : ℕ -> Term-λ

data Ctx-λ (A : 𝒰₀) : 𝒰₀ where
  [] : Ctx-λ A
  _,_ : Ctx-λ A -> Ty-λ A -> Ctx-λ A

Statement : 𝒰₀
Statement = ∑ λ n -> Judgement (Ctx-λ (Fin n)) (Ty-λ (Fin n))

instance
  isSet:Statement : isSet Statement
  isSet:Statement = record { fillPath-Set = {!!} }

instance
  isSetoid:Term : isSetoid _ Term-λ
  isSetoid:Term = setoid _≣_

data πVar : ∀{A} -> ℕ -> Ctx-λ A -> Ty-λ A -> 𝒰₁ where
  zero : ∀{A} -> ∀{Γ : Ctx-λ A} -> {τ : Ty-λ A} -> πVar 0 (Γ , τ) τ
  suc : ∀{A n} -> ∀{Γ : Ctx-λ A} -> {σ τ : Ty-λ A} -> πVar n Γ σ -> πVar (suc n) (Γ , τ) σ

data _∶_⊢_ : ∀{A} -> Term-λ -> Ctx-λ A -> Ty-λ A -> 𝒰₁ where
  var : ∀{A n} -> ∀{Γ : Ctx-λ A} {τ : Ty-λ A} -> πVar n Γ τ -> (var n) ∶ Γ ⊢ τ
  app : ∀{A} -> ∀{t s} -> ∀{Γ : Ctx-λ A} {τ σ : Ty-λ A} -> (t ∶ Γ ⊢ σ ⇒ τ) -> (s ∶ Γ ⊢ σ) -> (app s t ∶ Γ ⊢ τ)
  lam : ∀{A} -> ∀{t} -> ∀{Γ : Ctx-λ A} {τ σ : Ty-λ A} -> (t ∶ (Γ , σ) ⊢ τ) -> (lam t ∶ Γ ⊢ σ ⇒ τ)




