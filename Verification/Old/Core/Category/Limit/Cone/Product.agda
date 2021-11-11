
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Limit.Product where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Adjunction
open import Verification.Old.Core.Category.Limit.Definition



hasProducts : (X : 𝒰 𝑖) {{#X : ICategory X 𝑗}} -> 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺)
hasProducts X = has(⌘ 𝟚)ShapedLimits X

_×_ : {X : 𝒰 (𝑖)} {{_ : ICategory X 𝑗}} {{_ : hasProducts X}} (a b : X) -> X
_×_ {𝑖 = 𝑖} {𝑗 = 𝑗} a b = ⟨ ⟨ lim (free-Diagram (quiverHom (λ {₀ -> a ; ₁ -> b}))) ⟩ ⟩

Shape = SmallCategory
Shape:𝟚 : Shape
Shape:𝟚 = category 𝟚

-- TODO: Resolve: why do I need to do the following?
-- instance
-- ICone:FromLimit : {X : 𝒰 (𝑖)} {{_ : ICategory X 𝑗}} {{_ : hasProducts X}} -> {d : Diagram Shape:𝟚 (category X)} -> ICone d (⟨ ⟨ lim d ⟩ ⟩)
-- ICone:FromLimit {d = d} = of ⟨ lim d ⟩

-- instance
--   limi : ∀{S : SmallCategory} {X : 𝒰 𝑖} {𝑗} {{_ : ICategory X 𝑗}} {D : Diagram S (category X)} -> {{_ : has(S)ShapedLimits X}} -> Cone D
--   limi {D = D} = ⟨ lim D ⟩

π₀ : {X : 𝒰 (𝑖)} {{_ : ICategory X 𝑗}} {{_ : hasProducts X}} {a b : X} -> Hom (a × b) a
π₀ = ▲ {{of ⟨ lim _ ⟩}}

π₁ : {X : 𝒰 (𝑖)} {{_ : ICategory X 𝑗}} {{_ : hasProducts X}} {a b : X} -> Hom (a × b) b
π₁ = ▲ {{of ⟨ lim _ ⟩}}



