
module Verification.Core.Data.Universe.Instance.Semiring where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.Setoid
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


instance
  isMonoid:𝐔𝐧𝐢𝐯 : isMonoid (𝐔𝐧𝐢𝐯 𝑖)
  isMonoid:𝐔𝐧𝐢𝐯 = isMonoid:byHasFiniteCoproducts




