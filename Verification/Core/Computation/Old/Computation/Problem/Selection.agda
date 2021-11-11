
module Verification.Core.Theory.Computation.Problem.Selection where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Problem.Definition
open import Verification.Core.Theory.Computation.Problem.Codiscrete



module _ (A B : Problem 𝑖) where

  subsolution : (f : coDisc A ⟶ B) -> 𝒰 _
  subsolution f = ∑ λ (g : A ⟶ B) -> ⟨ f ⟩ ≡ ⟨ (ε-coDisc ◆ g) ⟩


--   Selection : 𝒰 _
--   Selection = (A ⟶ B)

