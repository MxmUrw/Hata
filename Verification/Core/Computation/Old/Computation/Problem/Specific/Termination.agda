
module Verification.Core.Theory.Computation.Problem.Specific.Termination where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Core.Category.Std.Category.As.Monoid
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Theory.Computation.Problem.Definition
-- open import Verification.Core.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat
-- open import Verification.Core.Theory.Computation.Problem.Paradigm.DivideAndConquer


record TerminationProblem (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  field Base : 𝒰 𝑖
  field step : Base -> Base
  field isDone : Base -> Bool

open TerminationProblem {{...}} public

data IterationStep (T : TerminationProblem 𝑖) : Base {{T}} -> 𝒰 𝑖 where
  done : ∀{a} -> isDone {{T}} a ≣ true -> IterationStep T a
  next : ∀{a b} -> step {{T}} a ≣ b -> IterationStep T b -> IterationStep T a

TerminationSolution : (T : TerminationProblem 𝑖) -> 𝒰 𝑖
TerminationSolution T = ∀ a -> IterationStep T a

TERMINATION : ∀ 𝑖 -> SomeStructure
TERMINATION 𝑖 = structureOn (TerminationProblem 𝑖)

-- 練 :

-- TERMINATION : 

instance
  isProblem:TERMINATION : ∀ {𝑖} -> isProblem _ (TERMINATION 𝑖)
  isProblem:TERMINATION = problem TerminationSolution

-- 練

-- record TerminationSolution (T : TerminationProblem 𝑖) : 𝒰 𝑖 where
--   field 



