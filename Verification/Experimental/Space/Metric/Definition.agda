
module Verification.Core.Space.Metric.Definition where

open import Verification.Conventions
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Rational.Definition
open import Verification.Core.Data.Rational.Inclusion
open import Verification.Core.Data.Real.Cauchy.Definition

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Ring.Localization
open import Verification.Core.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Core.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Core.Algebra.Field.Definition
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder

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




