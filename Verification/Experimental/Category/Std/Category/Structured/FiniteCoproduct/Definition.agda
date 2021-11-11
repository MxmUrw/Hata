
module Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

FiniteCoproductCategory : ∀ 𝑖 -> 𝒰 _
FiniteCoproductCategory 𝑖 = Category 𝑖 :& hasFiniteCoproducts


