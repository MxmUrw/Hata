
module Verification.Core.Theory.Formal.Specific.SimpleTypeTheory.Abstract.Checking where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Question.Definition
open import Verification.Core.Theory.Computation.Question.Specific.Check
open import Verification.Core.Theory.Computation.Question.Specific.Small
-- open import Verification.Core.Theory.Computation.Question.Codiscrete
-- open import Verification.Core.Theory.Computation.Question.Selection
-- open import Verification.Core.Theory.Computation.Question.Specific.Small

open import Verification.Core.Theory.Formal.Specific.SimpleTypeTheory.Definition as Λᶜ using ()
open import Verification.Core.Theory.Formal.Specific.SimpleTypeTheory.Definition using (_∣_⊢_ ; _∣_⊢_/_)


_∣_⊢_∶_ : Λᶜ.BCtx -> Λᶜ.FCtx -> Λᶜ.Term -> Λᶜ.Type -> 𝒰 _
_∣_⊢_∶_ = λ Γ Δ t τ -> Γ ∣ Δ ⊢ τ / t


-- Λᶜ-Typing : 𝒰 _
-- Λᶜ-Typing = ∑ λ Δ -> ∑ λ Γ -> ∑ λ τ -> Γ ∣ Δ ⊢ τ

Info-Λᶜ : 𝒰 _
Info-Λᶜ = Λᶜ.BCtx ×-𝒰 Λᶜ.FCtx ×-𝒰 Λᶜ.Type

_⊢ᶜ_ : Info-Λᶜ -> Λᶜ.Term -> 𝒰 _
_⊢ᶜ_ (Γ , Δ , τ) t = Γ ∣ Δ ⊢ t ∶ τ

Λᶜ : CHECK _
Λᶜ = check Λᶜ.Term (const Info-Λᶜ) (λ t (Γ , Δ , τ) → Γ ∣ Δ ⊢ t ∶ τ)

reduce-Λᶜ : CheckFam Λᶜ ⟶ TRIVIAL
reduce-Λᶜ = incl ((const tt) since reductive λ {(t , (Δ , Γ , τ))} _ → Λᶜ.check Δ Γ t τ)


-- so I want something like

-- reduce : Infer ΛCurry ⟶ Unify ΛCurry-Type

-- Λᶜ-Check : Check _
-- Λᶜ-Check = record
--   { Input = Λᶜ.Term
--   ; Answer = Λᶜ-Ctx
--   ; Correct = λ t (Δ , Γ , τ) → Δ ∣ Γ ⊢ τ
--   }



-- Λᶜ-check : coDisc 𝟙 ⟶ CHECK _
-- Λᶜ-check =
--   let f : 𝟙 -> CHECK _
--       f = const Λᶜ-Check
--   in incl (f since record { deduct = incl (λ ()) })

-- PPPP : subsolution 𝟙 (CHECK _) Λᶜ-check
-- PPPP = {!!} , {!!}


