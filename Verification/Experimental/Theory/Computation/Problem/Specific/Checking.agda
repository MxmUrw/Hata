
module Verification.Experimental.Theory.Computation.Problem.Specific.Checking where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition

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


