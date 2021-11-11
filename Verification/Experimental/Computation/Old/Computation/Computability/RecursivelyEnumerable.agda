
module Verification.Core.Theory.Computation.Computability.RecursivelyEnumerable where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category


𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
𝐂𝐚𝐭 𝑖 = structureOn (Category 𝑖)

data Bar {A : 𝒰 𝑖} (P : List A -> 𝒰 𝑗) : List A -> 𝒰 (𝑖 ､ 𝑗) where
  Done : ∀{as : List A} -> P as -> Bar P as
  Next : ∀{as : List A} -> (∀(a : A) -> Bar P (a ∷ as)) -> Bar P as

module _ {𝒞 𝒟 : 𝐂𝐚𝐭 𝑖} {F : 𝒞 ⟶ 𝒟} where


