
module Verification.Core.Data.Int.Definition where

open import Verification.Core.Conventions hiding (ℕ)

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Data.Nat.Definition

-- open import Verification.Conventions.Prelude.Data.Nat.Order renaming (_≟_ to compare-ℕ)

-- ℤ : SomeStructure
-- ℤ = structureOn Int

macro
  ℤ : SomeStructure
  ℤ = #structureOn Int

-- instance
--   isSetoid:ℤ : isSetoid _ Int
--   isSetoid._∼'_ isSetoid:ℤ = _≣_
--   isSetoid.isEquivRel:∼ isSetoid:ℤ = it







