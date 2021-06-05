
module Verification.Experimental.Theory.Computation.Problem.Specific.Small where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition


macro
  𝟘 : ∀{𝑖} -> SomeStructure
  𝟘 {𝑖} = #structureOn (⊥-𝒰 {𝑖})

  𝟙 : ∀{𝑖} -> SomeStructure
  𝟙 {𝑖} = #structureOn (⊤-𝒰 {𝑖})

instance
  isProblem:𝟙 : ∀{𝑖 𝑗} -> isProblem 𝑗 (𝟙 {𝑖})
  isProblem:𝟙 = problem λ x → 𝟙

instance
  isProblem:𝟘 : ∀{𝑖 𝑗} -> isProblem 𝑗 (𝟘 {𝑖})
  isProblem:𝟘 = problem λ ()



