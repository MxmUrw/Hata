
module Verification.Experimental.Data.Real.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.DedekindCompletion.Definition3
-- open import Verification.Experimental.Order.DedekindCompletion.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder

FFF : Linearorder (ℓ₀ , ℓ₀ , ℓ₀)
FFF = ′ ℚ ′

ℝ = Cut ′ ℚ ′ ℓ₀

-- mytest2 : ℝ -> ℝ -> 𝒰₀
-- mytest2 a b = a < b


