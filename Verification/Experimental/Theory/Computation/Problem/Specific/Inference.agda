
module Verification.Experimental.Theory.Computation.Problem.Specific.Inference where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition
open import Verification.Experimental.Theory.Computation.Problem.Specific.Checking


record InferenceProblem (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  field Base : 𝒰 (𝑖 ⌄ 0)
  field Solutions : Category 𝑖
  field {{isDiscrete:Solutions}} : isDiscrete ⟨ Solutions ⟩
  field hasTerminal:Solutions : ⟨ Solutions ⟩
  field forgetSolution : ⟨ Solutions ⟩ -> Base

open InferenceProblem public

record InferenceSolution (Π : InferenceProblem 𝑖) : 𝒰 𝑖 where
  field inferSolution : Π .Base -> ⟨ (Π .Solutions) ⟩
  field isSection : ∀ a -> Π .forgetSolution (inferSolution a) ≡ a

open InferenceSolution public

macro
  INFER : ∀ 𝑖 -> SomeStructure
  INFER 𝑖 = #structureOn (InferenceProblem 𝑖)

instance
  isProblem:INFER : ∀ {𝑖} -> isProblem _ (INFER 𝑖)
  isProblem:INFER = problem InferenceSolution


checkInfer : INFER 𝑖 -> CHECK _
checkInfer I = record
  { Questions = Base I
  ; Answers = λ i → ∑ λ (s : ⟨ Solutions I ⟩) -> forgetSolution I s ≣ i
  ; Correct = λ i (s , p) → s ≣ hasTerminal:Solutions I -> 𝟘-𝒰
  }

instance
  isDeductive:checkInfer : ∀{𝑖} -> isDeductive (INFER (𝑖 , 𝑖 , 𝑖)) (CHECK _) checkInfer
  isDeductive:checkInfer = record
    { deduct =
        let f : ∀{I} -> InferenceSolution I -> CheckingSolution (checkInfer I)
            f {I} IS = record
              { decideSolution = λ q a →
                 let b = inferSolution IS q
                 in case-Decision (b ≟-Str hasTerminal:Solutions I) of
                      {P = λ x -> isDecidable (checkInfer I .Correct q a)}
                      (λ x -> left {!!})
                      (λ x -> right {!!})
              }
        in incl f
    }

