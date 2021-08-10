
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
  field dist : ⟨ A ⟩ -> ⟨ A ⟩ -> ℝ
  field identify-dist : ∀{a b : ⟨ A ⟩} -> dist a b ∼ ◌ -> a ∼ b
  field id-dist : ∀{a b : ⟨ A ⟩} -> a ∼ b -> dist a b ∼ ◌
  field sym-dist : ∀{a b : ⟨ A ⟩} -> dist a b ∼ dist b a
  field tri-dist : ∀{a b c : ⟨ A ⟩} -> dist a c ≤ dist a b + dist b c

open isMetric {{...}} public




