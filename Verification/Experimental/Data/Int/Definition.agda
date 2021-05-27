
module Verification.Experimental.Data.Int.Definition where

open import Verification.Experimental.Conventions renaming (ℤ to Int)
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Algebra.Ring.Ordered

-- ℤ : SomeStructure
-- ℤ = structureOn Int

macro
  ℤ : SomeStructure
  ℤ = #structureOn Int

instance
  isSetoid:ℤ : isSetoid _ Int
  isSetoid._∼'_ isSetoid:ℤ = _≡_
  isSetoid.isEquivRel:∼ isSetoid:ℤ = it



instance
  isMonoid:ℤ : isMonoid ℤ
  isMonoid._⋆_ isMonoid:ℤ = _+-ℤ_
  isMonoid.◌ isMonoid:ℤ = pos 0
  isMonoid.unit-l-⋆ isMonoid:ℤ = incl (pos0+ _ ⁻¹)
  isMonoid.unit-r-⋆ isMonoid:ℤ = refl
  isMonoid.assoc-l-⋆ isMonoid:ℤ {a} {b} {c} = incl (assoc-+-ℤ a b c ⁻¹)
  isMonoid.assoc-r-⋆ isMonoid:ℤ {a} {b} {c} = incl (assoc-+-ℤ a b c)
  isMonoid._`cong-⋆`_ isMonoid:ℤ (incl p) (incl q) = incl $ λ i -> p i +-ℤ q i

  isCommutative:ℤ : isCommutative ℤ
  isCommutative.comm-⋆ isCommutative:ℤ {a} {b} = incl $ comm-+-ℤ a b

instance
  isGroup:ℤ : isGroup ℤ
  isGroup.◡_ isGroup:ℤ a = 0 -ℤ a
  isGroup.inv-l-⋆ isGroup:ℤ {a} = incl $ minusPlus a (pos 0)
  isGroup.inv-r-⋆ isGroup:ℤ {a} = comm-⋆ {a = a} ∙ (incl $ minusPlus a (pos 0))
  isGroup.cong-◡_ isGroup:ℤ (incl p) = incl $ λ i -> pos 0 -ℤ p i

open import Cubical.Data.Bool renaming (_⊕_ to _⊕-Bool_)

fromSign : Bool -> ℕ -> Int
fromSign false zero = pos 0
fromSign false (suc n) = negsuc n
fromSign true n = pos n

_⋅-ℤ_ : Int -> Int -> Int
a ⋅-ℤ b = fromSign (sgn a ⊕-Bool sgn b) (abs a *-ℕ abs b)

instance
  isSemiring:ℤ : isSemiring ℤ
  isSemiring._⋅_ isSemiring:ℤ = _⋅-ℤ_
  isSemiring.⨡ isSemiring:ℤ = pos 1
  isSemiring.unit-l-⋅ isSemiring:ℤ = {!!}
  isSemiring.unit-r-⋅ isSemiring:ℤ = {!!}
  isSemiring.assoc-l-⋅ isSemiring:ℤ = {!!}
  isSemiring.distr-l-⋅ isSemiring:ℤ = {!!}
  isSemiring.distr-r-⋅ isSemiring:ℤ = {!!}
  isSemiring._`cong-⋅`_ isSemiring:ℤ p q = {!!}

instance
  isRing:ℤ : isRing ℤ
  isRing:ℤ = record {}

instance
  isCRing:ℤ : isCRing ℤ
  isCRing.comm-⋅ isCRing:ℤ = {!!}

-- ta : ℤ
-- ta = pos 30 ⋅ pos 8

--------------------------------------------------------------------
-- Ordering

_<-ℤ_ : Int -> Int -> 𝒰 _
pos n <-ℤ pos m = n <-ℕ m
pos n <-ℤ negsuc m = 𝟘-𝒰
negsuc n <-ℤ pos m = 𝟙-𝒰
negsuc n <-ℤ negsuc m = m <-ℕ n

instance
  isLinearorder:ℤ : isLinearorder _ ℤ
  isLinearorder.my< isLinearorder:ℤ = _<-ℤ_
  isLinearorder.irrefl-< isLinearorder:ℤ = {!!}
  isLinearorder.asym-< isLinearorder:ℤ = {!!}
  isLinearorder.compare-< isLinearorder:ℤ = {!!}
  isLinearorder.connected-< isLinearorder:ℤ = {!!}
  isLinearorder.transp-< isLinearorder:ℤ = {!!}

instance
  isOrderedRing:ℤ : isOrderedRing _ ℤ
  isOrderedRing.OProof isOrderedRing:ℤ = isLinearorder:ℤ
  isOrderedRing.cong-⋆-<-r isOrderedRing:ℤ = {!!}
  isOrderedRing._⋅-isPositive_ isOrderedRing:ℤ = {!!}


