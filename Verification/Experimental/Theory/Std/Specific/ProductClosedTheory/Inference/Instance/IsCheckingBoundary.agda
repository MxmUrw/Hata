
module Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Instance.IsCheckingBoundary where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Substitution.Normal.Definition

open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Definition
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Module
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Instance.FormalSystem
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Instance.PCF
open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition

open import Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary

open import Verification.Experimental.Theory.Std.Presentation.CheckTree.Definition2
open import Verification.Experimental.Theory.Std.Presentation.CheckTree.FromUnification

macro
  ℬ : SomeStructure
  ℬ = #structureOn (♮𝐂𝐭𝐱ᵘ 𝒷)

instance
  is1Category:ℬΛ : is1Category ℬ
  is1Category:ℬΛ = {!!}

instance
  hasUnification:ℬ : hasUnification ℬ
  hasUnification:ℬ = {!!}

instance
  hasFiniteCoproducts:ℬ : hasFiniteCoproducts ℬ
  hasFiniteCoproducts:ℬ = {!!}


instance
  isCheckingBoundary:ℬΛ : ∀{a} -> isCheckingBoundary ℬ ((HomF (incl a)))
  isCheckingBoundary:ℬΛ = isCheckingBoundary:byUnification ℬ
