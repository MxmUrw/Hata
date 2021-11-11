
module Verification.Core.Computation.Question.Specific.Small where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
-- open import Verification.Core.Order.WellFounded.Definition
-- open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Computation.Question.Definition

data Trivial {𝑖} : 𝒰 𝑖 where
  tt : Trivial

instance
  isQuestion:Trivial : isQuestion 𝑗 (Trivial {𝑖})
  isQuestion:Trivial = answerWith (const ⊤-𝒰)

macro
  TRIVIAL : ∀ {𝑖} -> SomeStructure
  TRIVIAL {𝑖} = #structureOn (Trivial {𝑖})


