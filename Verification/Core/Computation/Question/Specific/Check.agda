
module Verification.Core.Computation.Question.Specific.Check where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Computation.Question.Definition

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


