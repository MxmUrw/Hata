
module Verification.Core.Data.Int.Instance.Ring where

open import Verification.Core.Conventions hiding (ℕ)

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
-- open import Verification.Core.Order.Linearorder
-- open import Verification.Core.Order.Preorder
-- open import Verification.Core.Order.Totalorder
-- open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Data.Nat.Definition
-- open import Verification.Core.Data.Nat.Instance.Order
open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Int.Instance.Monoid

-- open import Cubical.Data.Bool renaming (_⊕_ to _⊕-Bool_)

fromSign : Bool -> ℕ -> Int
fromSign false zero = pos 0
fromSign false (suc n) = negsuc n
fromSign true n = pos n

_⊗-Bool_ : Bool -> Bool -> Bool
_⊗-Bool_ a b = not (not a ⊕-Bool not b)

_⋅-ℤ_ : Int -> Int -> Int
a ⋅-ℤ b = fromSign (sgn a ⊗-Bool sgn b) (abs a *-ℕ abs b)

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
-- open import Cubical.Data.Bool renaming (_⊕_ to _⊕-Bool_)

instance
  isCRing:ℤ : isCRing ℤ
  isCRing:ℤ = {!!}


-- ta : ℤ
-- ta = pos 30 ⋅ pos 8
