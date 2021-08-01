
module Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

FiniteCoproductCategory : ∀ 𝑖 -> 𝒰 _
FiniteCoproductCategory 𝑖 = Category 𝑖 :& hasFiniteCoproducts


