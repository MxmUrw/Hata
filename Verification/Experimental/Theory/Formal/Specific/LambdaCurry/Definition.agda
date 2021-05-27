
module Verification.Experimental.Theory.Formal.Specific.LambdaCurry.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Theory.Formal.Presentation.Signature.SingleSorted.Definition

data TySig : ℕ -> 𝒰₀ where
  `ℕ` `𝔹` : TySig 0
  `⇒` : TySig 2


-- Defining types

Ty-λ : 𝒰₀ -> 𝒰₀
Ty-λ = Term TySig

infixr 50 _⇒_
pattern _⇒_ σ τ = te `⇒` (σ ∷ τ ∷ [])


data Term-λ : 𝒰₀ where
  app : (f g : Term-λ) -> Term-λ
  lam : (t : Term-λ) -> Term-λ
  var : ℕ -> Term-λ

data Ctx-λ (A : 𝒰₀) : 𝒰₀ where
  [] : Ctx-λ A
  _,_ : Ctx-λ A -> Ty-λ A -> Ctx-λ A

data πVar : ∀{A} -> ℕ -> Ctx-λ A -> Ty-λ A -> 𝒰₁ where
  zero : ∀{A} -> ∀{Γ : Ctx-λ A} -> {τ : Ty-λ A} -> πVar 0 (Γ , τ) τ
  suc : ∀{A n} -> ∀{Γ : Ctx-λ A} -> {σ τ : Ty-λ A} -> πVar n Γ σ -> πVar (suc n) (Γ , τ) σ

data _∶_⊢_ : ∀{A} -> Term-λ -> Ctx-λ A -> Ty-λ A -> 𝒰₁ where
  var : ∀{A n} -> ∀{Γ : Ctx-λ A} {τ : Ty-λ A} -> πVar n Γ τ -> (var n) ∶ Γ ⊢ τ
  app : ∀{A} -> ∀{t s} -> ∀{Γ : Ctx-λ A} {τ σ : Ty-λ A} -> (t ∶ Γ ⊢ σ ⇒ τ) -> (s ∶ Γ ⊢ σ) -> (app s t ∶ Γ ⊢ τ)
  lam : ∀{A} -> ∀{t} -> ∀{Γ : Ctx-λ A} {τ σ : Ty-λ A} -> (t ∶ (Γ , σ) ⊢ τ) -> (lam t ∶ Γ ⊢ σ ⇒ τ)




