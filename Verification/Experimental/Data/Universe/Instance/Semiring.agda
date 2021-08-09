
module Verification.Experimental.Data.Universe.Instance.Semiring where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.Setoid
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition


instance
  isMonoid:𝐔𝐧𝐢𝐯 : isMonoid (𝐔𝐧𝐢𝐯 𝑖)
  isMonoid:𝐔𝐧𝐢𝐯 = isMonoid:byHasFiniteCoproducts




