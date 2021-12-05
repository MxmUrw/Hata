
module Verification.Core.Theory.Computation.Problem.Specific.Small where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Problem.Definition


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



