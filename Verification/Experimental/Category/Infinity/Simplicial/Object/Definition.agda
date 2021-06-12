
module Verification.Experimental.Category.Infinity.Simplicial.Object.Definition where

open import Verification.Conventions

open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Set.Finite.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Totalorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Representable
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Infinity.Simplicial.Simplex.Definition

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


