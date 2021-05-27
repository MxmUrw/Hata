
module Verification.Experimental.Category.Infinity.Simplicial.Simplex.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Finite.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Totalorder
open import Verification.Experimental.Category.Std.Category.Definition

record isSimplex (A : 𝒰 _ :& (is Finite _) :, (is Totalorder⁺ 𝑖)) : 𝒰 𝑖 where
instance
  isSimplex:Anything : ∀{A : 𝒰 𝑖}
                       -> {{_ : isDiscrete' A}} -> {{_ : isFinite ′ A ′}}
                       -> {{_ : isSetoid 𝑙 A }}
                       -> {{_ : isPreorder 𝑘 ′ A ′ }}
                       -> {{_ : isPartialorder ′ A ′ }}
                       -> {{_ : isTotalorder⁺ ′ A ′}}
                       -> isSimplex ′ A ′
  isSimplex:Anything = record {}

-- isSimplex : (A : 𝒰 _ :& (is Finite _) :, (is Totalorder⁺ 𝑖)) : 𝒰 𝑖 where

Simplex : ∀(𝑖) -> 𝒰 _
Simplex 𝑖 = _ :& isSimplex {𝑖 = 𝑖}

instance
  isCategory:Simplex : isCategory _ (Simplex 𝑖)
  isCategory.Hom' isCategory:Simplex A B = Monotone ′ ⟨ A ⟩ ′ ′ ⟨ B ⟩ ′
  isSetoid._∼'_ (isCategory.isSetoid:Hom isCategory:Simplex) f g = ⟨ f ⟩ ∼' ⟨ g ⟩
  isSetoid.isEquivRel:∼ (isCategory.isSetoid:Hom isCategory:Simplex) = {!!}
  isCategory.id isCategory:Simplex = {!!}
  isCategory._◆_ isCategory:Simplex = {!!}
  isCategory.unit-l-◆ isCategory:Simplex = {!!}
  isCategory.unit-r-◆ isCategory:Simplex = {!!}
  isCategory.unit-2-◆ isCategory:Simplex = {!!}
  isCategory.assoc-l-◆ isCategory:Simplex = {!!}
  isCategory.assoc-r-◆ isCategory:Simplex = {!!}
  isCategory._◈_ isCategory:Simplex = {!!}


∆L : ∀ 𝑖 -> Category _
∆L 𝑖 = ′ Simplex 𝑖 ′




