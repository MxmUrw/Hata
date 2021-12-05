
module Verification.Core.Theory.Computation.Problem.Specific.Checking where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Problem.Definition

record CheckingProblem (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  field Questions : 𝒰 (𝑖 ⌄ 0)
  field Answers : Questions -> 𝒰 (𝑖 ⌄ 1)
  field Correct : (q : Questions) -> Answers q -> 𝒰 (𝑖 ⌄ 2)
  -- field Base : 𝒰 (𝑖 ⌄ 0)
  -- field Solutions : Category 𝑖
  -- field forgetSolution : ⟨ Solutions ⟩ -> Base

open CheckingProblem public

record CheckingSolution (Π : CheckingProblem 𝑖) : 𝒰 𝑖 where
  field decideSolution : ∀ q a -> isDecidable (Π .Correct q a)

macro
  CHECK : ∀ 𝑖 -> SomeStructure
  CHECK 𝑖 = #structureOn (CheckingProblem 𝑖)

instance
  isProblem:CHECK : ∀ {𝑖} -> isProblem _ (CHECK 𝑖)
  isProblem:CHECK = problem CheckingSolution


