
module Verification.Core.Theory.Computation.Question.Specific.Infer where

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
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Theory.Computation.Question.Definition

record Infer (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺) where
  constructor infer
  field Input : 𝒰 (𝑖 ⌄ 0)
  field Info : Input -> Category (𝑖 ⌄ 1 , 𝑖 ⌄ 2 , 𝑖 ⌄ 3)

  -- field forget : ⟨ Info ⟩ -> Input
  -- Sum : Input -> 𝒰 _
  -- Sum i = ∑ λ (x : ⟨ Info ⟩) -> forget x ≣ i
  -- πSum : ∀ i -> Sum i -> ⟨ Info ⟩
  -- πSum i (x , _) = x

open Infer public

  -- field Answer : Input -> 
  -- field 
  -- field isCorrect : (i : Input) -> (a : Answer i) -> 𝒰 (𝑖 ⌄ 4)

-- open Check public

macro
  INFER : ∀ 𝑖 -> SomeStructure
  INFER 𝑖 = #structureOn (Infer 𝑖)

-- -- record CheckingSolution (Π : CheckingQuestion 𝑖) : 𝒰 𝑖 where
-- --   field decideSolution : ∀ q a -> isDecidable (Π .Correct q a)

record hasInitial (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field ⊥ : ⟨ 𝒞 ⟩
  field initial-⊥ : ∀{a} -> ⊥ ⟶ a

instance
  isQuestion:INFER : ∀ {𝑖} -> isQuestion _ (INFER 𝑖)
  isQuestion:INFER = answerWith λ (inf) → ∀ (i : Input inf) -> hasInitial (Info inf i)

  -- λ q → ∀ i a -> isDecidable (isCorrect q i a)

-- CheckFam : Check 𝑖 -> 𝐐𝐮𝐞𝐬𝐭 _
-- CheckFam (check i a c) = (∑ a) since answerWith (λ (i , a) → isDecidable (c i a))

-- instance
--   isReductive:CheckFam : isReductive (INFER 𝑖) (𝐐𝐮𝐞𝐬𝐭 _) CheckFam
--   isReductive:CheckFam = reductive λ x i a → x (i , a)
