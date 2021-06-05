
module Verification.Experimental.Theory.Computation.Problem.Selection where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition
open import Verification.Experimental.Theory.Computation.Problem.Codiscrete



module _ (A B : Problem 𝑖) where

  subsolution : (f : coDisc A ⟶ B) -> 𝒰 _
  subsolution f = ∑ λ (g : A ⟶ B) -> ⟨ f ⟩ ≡ ⟨ (ε-coDisc ◆ g) ⟩


--   Selection : 𝒰 _
--   Selection = (A ⟶ B)

