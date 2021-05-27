
module Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Abstract.Checking where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition
open import Verification.Experimental.Theory.Computation.Problem.Codiscrete
open import Verification.Experimental.Theory.Computation.Problem.Selection
open import Verification.Experimental.Theory.Computation.Problem.Specific.Checking
open import Verification.Experimental.Theory.Computation.Problem.Specific.Small

open import Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Definition as Λ
open import Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Definition using (_∣_⊢_)


Λ-Typing : 𝒰 _
Λ-Typing = ∑ λ Δ -> ∑ λ Γ -> ∑ λ τ -> Γ ∣ Δ ⊢ τ

Λ-Ctx : 𝒰 _
Λ-Ctx = Λ.BCtx ×-𝒰 Λ.FCtx ×-𝒰 Λ.Type

Λ-Check : CheckingProblem _
Λ-Check = record
  { Questions = Λ.Term
  ; Answers = Λ-Ctx
  ; Correct = λ t (Δ , Γ , τ) → Δ ∣ Γ ⊢ τ
  }


pattern _since_ a b = ′ a ′ {{b}}

Λ-check : coDisc 𝟙 ⟶ CHECK _
Λ-check =
  let f : 𝟙 -> CHECK _
      f = const Λ-Check
  in incl (f since record { deduct = incl (λ ()) })

PPPP : subsolution 𝟙 (CHECK _) Λ-check
PPPP = {!!} , {!!}


