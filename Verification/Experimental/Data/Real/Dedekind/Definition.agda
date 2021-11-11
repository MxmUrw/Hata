
module Verification.Core.Data.Real.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Rational.Definition

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.DedekindCompletion.Definition3
-- open import Verification.Core.Order.DedekindCompletion.Instance.Linearorder
open import Verification.Core.Algebra.Ring.Localization.Instance.Linearorder

-- FFF : Linearorder (ℓ₀ , ℓ₀ , ℓ₀)
-- FFF = ℚ


ℝᵘ = Cut ℚ ℓ₀

macro ℝ = #structureOn ℝᵘ

-- mytest2 : ℝ -> ℝ -> 𝒰₀
-- mytest2 a b = a < b


