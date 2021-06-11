
module Verification.Experimental.Computation.Question.Specific.Small where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
-- open import Verification.Experimental.Order.WellFounded.Definition
-- open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Computation.Question.Definition

data Trivial {𝑖} : 𝒰 𝑖 where
  tt : Trivial

instance
  isQuestion:Trivial : isQuestion 𝑗 (Trivial {𝑖})
  isQuestion:Trivial = answerWith (const ⊤-𝒰)

macro
  TRIVIAL : ∀ {𝑖} -> SomeStructure
  TRIVIAL {𝑖} = #structureOn (Trivial {𝑖})


