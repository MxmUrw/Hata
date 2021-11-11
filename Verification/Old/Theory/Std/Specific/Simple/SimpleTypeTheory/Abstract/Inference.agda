
module Verification.Core.Theory.Formal.Specific.SimpleTypeTheory.Abstract.Inference where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Problem.Definition
open import Verification.Core.Theory.Computation.Problem.Specific.Inference

open import Verification.Core.Theory.Formal.Specific.SimpleTypeTheory.Definition as Λ
open import Verification.Core.Theory.Formal.Specific.SimpleTypeTheory.Definition using (_∣_⊢_)


Λ-Typing : 𝒰 _
Λ-Typing = ∑ λ Δ -> ∑ λ Γ -> ∑ λ τ -> Γ ∣ Δ ⊢ τ

instance
  isCategory:Λ-Typing : isCategory (ℓ₀ , ℓ₀) (Λ-Typing)
  isCategory:Λ-Typing = {!!}

Λ-Inf : InferenceProblem _
Λ-Inf = record
  { Base = Λ.Term
  ; Solutions = ′ Λ-Typing ′
  ; forgetSolution = λ (_ , _ , _ , t) → {!!}
  }

-- module _ where
--   private
--     lem-1 : ∀{x : 𝟙 ⟶ Λ-Inf} -> 𝟙 ⟶ Λ-Check





