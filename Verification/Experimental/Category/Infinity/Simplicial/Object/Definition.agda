
module Verification.Core.Category.Infinity.Simplicial.Object.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Finite.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Set.Discrete
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Representable
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Infinity.Simplicial.Simplex.Definition

Simplicial : ∀ 𝑗 -> (𝒞 : Category 𝑖) -> 𝒰 _
Simplicial 𝑗 𝒞 = Functor (∆L 𝑗 ᵒᵖ) 𝒞


∆Std : ∀ 𝑗 𝑖 -> 𝒰 _
∆Std 𝑗 𝑖 = Simplicial 𝑗 (Std 𝑖)


-- now we want to build examples
∆[_] : ∀(n : ℕ) -> ∆Std _ _
∆[ n ] = ′ [_, ′ Fin n ′ ]𝓈 ′

-- sss = ∆[ 0 ]

-- now, by yoneda, we have
lem-10 : ∀{X : ∆Std _ _} -> (⟨ X ⟩ ′ Fin n ′) ≅𝓈 [ ∆[ n ] , X ]𝓈
lem-10 = {!!}


