
module Verification.Experimental.Theory.Computation.Problem.Specific.Termination where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition
-- open import Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat
-- open import Verification.Experimental.Theory.Computation.Problem.Paradigm.DivideAndConquer


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



