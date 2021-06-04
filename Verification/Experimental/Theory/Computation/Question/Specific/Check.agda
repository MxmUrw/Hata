
module Verification.Experimental.Theory.Computation.Question.Specific.Check where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Question.Definition

record Check (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  constructor check
  field Input : 𝒰 (𝑖 ⌄ 0)
  field Answer : Input -> 𝒰 (𝑖 ⌄ 1)
  field isCorrect : (i : Input) -> (a : Answer i) -> 𝒰 (𝑖 ⌄ 2)

open Check public

macro
  CHECK : ∀ 𝑖 -> SomeStructure
  CHECK 𝑖 = #structureOn (Check 𝑖)

-- record CheckingSolution (Π : CheckingQuestion 𝑖) : 𝒰 𝑖 where
--   field decideSolution : ∀ q a -> isDecidable (Π .Correct q a)

instance
  isQuestion:CHECK : ∀ {𝑖} -> isQuestion _ (CHECK 𝑖)
  isQuestion:CHECK = answerWith λ q → ∀ i a -> isDecidable (isCorrect q i a)

CheckFam : Check 𝑖 -> 𝐐𝐮𝐞𝐬𝐭 _
CheckFam (check i a c) = (∑ a) since answerWith (λ (i , a) → isDecidable (c i a))

instance
  isReductive:CheckFam : isReductive (CHECK 𝑖) (𝐐𝐮𝐞𝐬𝐭 _) CheckFam
  isReductive:CheckFam = reductive λ x i a → x (i , a)


