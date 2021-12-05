
module Verification.Core.Theory.Std.Specific.Simple.LambdaChurch.Definition where

open import Verification.Core.Conventions hiding (isSet)
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Theory.Std.Presentation.Signature.SingleSorted.Definition as SingleSorted
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

-- data TySig : ℕ -> 𝒰₀ where
--   `ℕ` `𝔹` : TySig 0
--   `⇒` : TySig 2


-- Defining types

-- Ty-λ : 𝒰₀ -> 𝒰₀
-- Ty-λ = SingleSorted.Term TySig

-- infixr 50 _⇒_
-- pattern _⇒_ σ τ = te `⇒` (σ ∷ τ ∷ [])


data Ty-λ {𝑖} : 𝒰 𝑖 where
  `ℕ` `𝔹` : Ty-λ
  _`⇒`_ : Ty-λ {𝑖} -> Ty-λ {𝑖} -> Ty-λ



data Term-λ : ℕ -> 𝒰₀ where
  app : (f g : Term-λ n) -> Term-λ n
  lam : Ty-λ -> (t : Term-λ (suc n)) -> Term-λ n
  var : 𝔽ʳ n -> Term-λ n
  zero : Term-λ n
  suc : Term-λ n -> Term-λ n
  false true : Term-λ n
  rec-ℕ : Ty-λ -> Term-λ (suc n) -> Term-λ n -> Term-λ n -> Term-λ n

-- data SCtx (A : 𝒰₀) : 𝒰₀ where
--   [] : SCtx A
--   _,_ : SCtx A -> Ty-λ A -> SCtx A


instance
  IBootEq:⊥ : ∀{𝑖} -> IBootEq {𝑖} (Ty-λ)
  IBootEq._≟_ IBootEq:⊥ = f
    where f : Ty-λ → Ty-λ → Bool
          f `ℕ` `ℕ` = true
          f `𝔹` `𝔹` = true
          f (a `⇒` a₁) (b `⇒` b₁) = f a b and f a₁ b₁
          f _ _ = false

-- instance
--   IBootEq:SCtx : ∀{A} -> {{_ : IBootEq A}} -> IBootEq (SCtx A)
--   IBootEq:SCtx = {!!}

-- instance
--   IBootEq:TySig : IBootEq (TySig n)
--   IBootEq:TySig = {!!}

-- instance
--   IBootEq:Term : ∀{A σ} -> {{_ : IBootEq A}} -> {{∀ {n} -> IBootEq (σ n)}} -> IBootEq (SingleSorted.Term {𝑖} σ A)
--   IBootEq:Term = {!!}

-- Info : 𝒰₀
-- Info = Jdg-⦿ (Ty-λ ⊥)
-- -- (SCtx ⊥) 

-- Statement : 𝒰₀
-- Statement = ∑ λ n -> Jdg-⦿ (Ty-λ (Fin n))
-- -- (SCtx (Fin n)) 

-- instance
--   isSet:Statement : isSet Statement
--   isSet:Statement = record { fillPath-Set = {!!} }

-- instance
--   isSetoid:Term : isSetoid _ Term-λ
--   isSetoid:Term = isSetoid:byDef _≣_

-- data πVar : ∀{A} -> ℕ -> SCtx A -> Ty-λ A -> 𝒰₁ where
--   zero : ∀{A} -> ∀{Γ : SCtx A} -> {τ : Ty-λ A} -> πVar 0 (Γ , τ) τ
--   suc : ∀{A n} -> ∀{Γ : SCtx A} -> {σ τ : Ty-λ A} -> πVar n Γ σ -> πVar (suc n) (Γ , τ) σ

-- data _∶_⊢_ : ∀{A} -> Term-λ -> SCtx A -> Ty-λ A -> 𝒰₁ where
--   var : ∀{A n} -> ∀{Γ : SCtx A} {τ : Ty-λ A} -> πVar n Γ τ -> (var n) ∶ Γ ⊢ τ
--   app : ∀{A} -> ∀{t s} -> ∀{Γ : SCtx A} {τ σ : Ty-λ A} -> (t ∶ Γ ⊢ σ ⇒ τ) -> (s ∶ Γ ⊢ σ) -> (app s t ∶ Γ ⊢ τ)
--   lam : ∀{A} -> ∀{t} -> ∀{Γ : SCtx A} {τ σ : Ty-λ A} -> (t ∶ (Γ , σ) ⊢ τ) -> (lam t ∶ Γ ⊢ σ ⇒ τ)


