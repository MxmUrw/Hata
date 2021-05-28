
module Verification.Conventions.Proprelude.CubicalConventions where

open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )

open import Agda.Builtin.Sigma

_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

infixr 5 _×_

infixr 3 _∘_
_∘_ : ∀ {ℓ ℓ' ℓ''} -> ∀{A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} -> (f : B -> C) -> (g : A -> B) -> A -> C
_∘_ f g x = f (g x)


case_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → (x : A) → (∀ x → B x) → B x
case x of f = f x
{-# INLINE case_of_ #-}

case_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') → (∀ x → B x) → B x
case x return P of f = f x
{-# INLINE case_return_of_ #-}

-- -- Σ-types
-- infix 2 Σ-syntax

-- Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
-- Σ-syntax = Σ

-- syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
