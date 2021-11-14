
module Verification.Core.Algebra.Pointed.Instance.FiniteCoproductCategory where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Algebra.Pointed.Definition
open import Verification.Core.Algebra.Pointed.Instance.Category

instance
  isPointed:⊤-𝒰 : isPointed (⊤-𝒰 {𝑖})
  isPointed:⊤-𝒰 = record { pt = tt }

0-𝐏𝐭𝐝 : Pointed 𝑖
0-𝐏𝐭𝐝 = ′ ⊤-𝒰 ′

----------------------------------------------------------
-- we show that ⊤ is the initial and terminal object in 𝐏𝐭𝐝

elim-0-𝐏𝐭𝐝 : ∀{a : 𝐏𝐭𝐝 𝑖} -> 0-𝐏𝐭𝐝 ⟶ a
elim-0-𝐏𝐭𝐝 = const pt since isPointedHom:byDefinition refl-≡

instance
  isInitial:⊤-𝒰 : isInitial (0-𝐏𝐭𝐝 {𝑖})
  isInitial:⊤-𝒰 = record { elim-⊥ = elim-0-𝐏𝐭𝐝 ; expand-⊥ = {!!} }

instance
  hasInitial:𝐏𝐭𝐝 : hasInitial (𝐏𝐭𝐝 𝑖)
  hasInitial:𝐏𝐭𝐝 = record { ⊥ = 0-𝐏𝐭𝐝 }





