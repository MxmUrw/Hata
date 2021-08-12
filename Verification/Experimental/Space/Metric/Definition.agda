
module Verification.Experimental.Space.Metric.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Data.Rational.Inclusion
open import Verification.Experimental.Data.Real.Cauchy.Definition

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Ordered
open import Verification.Experimental.Algebra.Ring.Localization
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Experimental.Algebra.Field.Definition
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.Preorder

open AbelianMonoidNotation


record isMetric (A : Setoid 𝑖) : 𝒰 𝑖 where
  constructor metric
  infix 70 _⎓_
  field _⎓_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ℝ
  field identify-⎓ : ∀{a b : ⟨ A ⟩} -> a ⎓ b ∼ ◌ -> a ∼ b
  field id-⎓ : ∀{a b : ⟨ A ⟩} -> a ∼ b -> a ⎓ b ∼ ◌
  field sym-⎓ : ∀{a b : ⟨ A ⟩} -> a ⎓ b ∼ b ⎓ a
  field tri-⎓ : ∀{a b c : ⟨ A ⟩} -> a ⎓ c ≤ a ⎓ b + b ⎓ c

open isMetric {{...}} public




