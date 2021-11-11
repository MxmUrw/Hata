
module Verification.Core.Theory.Std.Specific.ProductClosedTheory.Inference.Instance.IsCheckingBoundary where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.Monoid.Free.Element
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Substitution.Normal.Definition

open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Theory.Std.Presentation.Token.Definition
open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Definition
-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.FormalSystem
open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.PCF
open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition

open import Verification.Core.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary

open import Verification.Core.Theory.Std.Presentation.CheckTree.Definition2
open import Verification.Core.Theory.Std.Presentation.CheckTree.FromUnification

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
