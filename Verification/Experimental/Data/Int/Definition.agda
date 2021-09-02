
module Verification.Experimental.Data.Int.Definition where

open import Verification.Experimental.Conventions hiding (ℕ)

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Totalorder
open import Verification.Experimental.Algebra.Ring.Ordered
open import Verification.Experimental.Data.Nat.Definition

-- open import Verification.Conventions.Prelude.Data.Nat.Order renaming (_≟_ to compare-ℕ)

-- ℤ : SomeStructure
-- ℤ = structureOn Int

macro
  ℤ : SomeStructure
  ℤ = #structureOn Int

-- instance
--   isSetoid:ℤ : isSetoid _ Int
--   isSetoid._∼'_ isSetoid:ℤ = _≣_
--   isSetoid.isEquivRel:∼ isSetoid:ℤ = it



instance
  isMonoid:ℤ : isMonoid ℤ
  isMonoid._⋆_ isMonoid:ℤ = _+-ℤ_
  isMonoid.◌ isMonoid:ℤ = pos 0
  isMonoid.unit-l-⋆ isMonoid:ℤ = (pos0+ _ ⁻¹)
  isMonoid.unit-r-⋆ isMonoid:ℤ = refl
  isMonoid.assoc-l-⋆ isMonoid:ℤ {a} {b} {c} = (assoc-+-ℤ a b c ⁻¹)
  -- isMonoid.assoc-r-⋆ isMonoid:ℤ {a} {b} {c} = (assoc-+-ℤ a b c)
  isMonoid._`cong-⋆`_ isMonoid:ℤ (p) (q) = {!!} -- incl $ λ i -> p i +-ℤ q i

  isCommutative:ℤ : isCommutative ℤ
  isCommutative.comm-⋆ isCommutative:ℤ {a} {b} = comm-+-ℤ a b

instance
  isGroup:ℤ : isGroup ℤ
  isGroup.◡_ isGroup:ℤ a = _-ℤ_ 0 a
  isGroup.inv-l-⋆ isGroup:ℤ {a} = minusPlus a (pos 0)
  isGroup.inv-r-⋆ isGroup:ℤ {a} = comm-⋆ {a = a} ∙ (minusPlus a (pos 0))
  isGroup.cong-◡_ isGroup:ℤ (p) = {!!} -- incl $ λ i -> pos 0 -ℤ p i

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

instance
  isCRing:ℤ : isCRing ℤ
  isCRing.comm-⋅ isCRing:ℤ = {!!}

-- ta : ℤ
-- ta = pos 30 ⋅ pos 8

--------------------------------------------------------------------
-- Ordering

data _<-ℤ_ : Int -> Int -> 𝒰₀ where
  pos : ∀{m n} -> m <-ℕ n -> pos m <-ℤ pos n
  negsuc : ∀{m n} -> m <-ℕ n -> negsuc n <-ℤ negsuc m
  negsucpos : ∀{m n} -> negsuc m <-ℤ pos n

data _≤-ℤ_ : Int -> Int -> 𝒰₀ where
  pos : ∀{m n} -> m ≤ n -> pos m ≤-ℤ pos n
  negsuc : ∀{m n} -> m ≤ n -> negsuc n ≤-ℤ negsuc m
  negsucpos : ∀{m n} -> negsuc m ≤-ℤ pos n



-- pos n <-ℤ pos m = n <-ℕ m
-- pos n <-ℤ negsuc m = 𝟘-𝒰
-- negsuc n <-ℤ pos m = 𝟙-𝒰
-- negsuc n <-ℤ negsuc m = m <-ℕ n

-- _<-ℤ_ : Int -> Int -> 𝒰 _
-- pos n <-ℤ pos m = n <-ℕ m
-- pos n <-ℤ negsuc m = 𝟘-𝒰
-- negsuc n <-ℤ pos m = 𝟙-𝒰
-- negsuc n <-ℤ negsuc m = m <-ℕ n

-- compare-<-ℕ : {a c : ℕ} -> (Base< _<-ℕ_ a c) -> (b : ℕ) -> (Base< _<-ℕ_ a b) +-𝒰 (Base< _<-ℕ_ b c)
-- compare-<-ℕ {a} {c} p b with compare-ℕ a b | compare-ℕ b c
-- ... | lt x | Y = left (incl x)
-- ... | eq refl-StrId | Y = right p
-- ... | gt x | lt y = right (incl y)
-- ... | gt x | eq refl-StrId = left p
-- ... | gt x | gt y = 𝟘-rec (¬m<m (<-trans (<-trans (Base<.Proof p) y) x))


-- compare-<-ℤ : {a c : ℤ} -> (Base< _<-ℤ_ a c) -> (b : ℤ) -> (Base< _<-ℤ_ a b) +-𝒰 (Base< _<-ℤ_ b c)
-- compare-<-ℤ {.(pos _)} {.(pos _)} (incl (pos x)) (pos n) with compare-<-ℕ (incl x) n
-- ... | left (incl q) = left (incl (pos q))
-- ... | just (incl q) = right (incl (pos q))
-- compare-<-ℤ {.(pos _)} {.(pos _)} (incl (pos x)) (negsuc n) = right (incl negsucpos)
-- compare-<-ℤ {.(negsuc _)} {.(negsuc _)} (incl (negsuc x)) (pos n) = left (incl negsucpos)
-- compare-<-ℤ {.(negsuc _)} {.(negsuc _)} (incl (negsuc x)) (negsuc n) with compare-<-ℕ (incl x) n
-- ... | left (incl q) = right (incl (negsuc q))
-- ... | just (incl q) = left (incl (negsuc q))
-- compare-<-ℤ {.(negsuc _)} {.(pos _)} (incl negsucpos) (pos n) = left (incl negsucpos)
-- compare-<-ℤ {.(negsuc _)} {.(pos _)} (incl negsucpos) (negsuc n) = right (incl negsucpos)


instance
  isPreorder:ℤ : isPreorder _ ℤ
  isPreorder:ℤ = record
    { _≤_ = ≤-Base _≤-ℤ_
    ; reflexive = lem-10
    ; _⟡_ = lem-20
    ; transp-≤ = lem-30
    }
    where
      _≤1_ : ℤ -> ℤ -> 𝒰 _
      _≤1_ = ≤-Base _≤-ℤ_

      lem-10 : ∀{a : ℤ} -> a ≤1 a
      lem-10 {pos n} = incl (pos reflexive)
      lem-10 {negsuc n} = incl (negsuc reflexive)

      lem-20 : ∀{a b c : ℤ} -> a ≤1 b -> b ≤1 c -> a ≤1 c
      lem-20 (incl (pos p)) (incl (pos q)) = incl (pos (p ⟡ q))
      lem-20 (incl (negsuc p)) (incl (negsuc q)) = incl (negsuc (q ⟡ p))
      lem-20 (incl (negsuc p)) (incl negsucpos) = incl negsucpos
      lem-20 (incl negsucpos) (incl (pos q)) = incl negsucpos

      lem-30 : ∀{a0 a1 b0 b1 : ℤ} -> a0 ∼ a1 -> b0 ∼ b1 -> a0 ≤1 b0 -> a1 ≤1 b1
      lem-30 (refl-StrId) (refl-StrId) r = r

instance
  isPartialorder:ℤ : isPartialorder ℤ
  isPartialorder:ℤ = record
    { antisym = lem-10
    }
    where
      _≤1_ : ℤ -> ℤ -> 𝒰 _
      _≤1_ = ≤-Base _≤-ℤ_

      lem-10 : ∀{a b} -> a ≤1 b -> b ≤1 a -> a ∼ b
      lem-10 (incl (pos p)) (incl (pos q)) = (cong-Str pos (antisym p q))
      lem-10 (incl (negsuc p)) (incl (negsuc q)) = (cong-Str negsuc (antisym q p))

instance
  isTotalorder⁺:ℤ : isTotalorder⁺ ℤ
  isTotalorder⁺:ℤ = record
    { total⁺ = lem-10
    }
    where
      _≤1_ : ℤ -> ℤ -> 𝒰 _
      _≤1_ = ≤-Base _≤-ℤ_

      lem-10 : ∀(a b : ℤ) -> Trichotomy' ℤ a b
      lem-10 (pos m) (pos n) with total⁺ m n
      ... | lt (x , p) = lt ((incl (pos x)) , λ {(refl-StrId) → p (refl-StrId)})
      ... | eq (refl-StrId) = eq (refl-StrId)
      ... | gt (x , p) = gt ((incl (pos x)) , λ {(refl-StrId) → p (refl-StrId)})
      lem-10 (pos n) (negsuc n₁) = gt ((incl negsucpos) , (λ ()))
      lem-10 (negsuc n) (pos n₁) = lt ((incl negsucpos) , (λ ()))
      lem-10 (negsuc m) (negsuc n) with total⁺ m n
      ... | lt (x , p) = gt ((incl (negsuc x)) , λ {(refl-StrId) → p (refl-StrId)})
      ... | eq (refl-StrId) = eq (refl-StrId)
      ... | gt (x , p) = lt ((incl (negsuc x)) , λ {(refl-StrId) → p (refl-StrId)})


instance
  isLinearorder:ℤ : isLinearorder _ ℤ
  isLinearorder:ℤ = isLinearorder:Totalorder⁺ ℤ

instance
  isOrderedRing:ℤ : isOrderedRing _ ℤ
  isOrderedRing.OProof isOrderedRing:ℤ = isLinearorder:ℤ
  isOrderedRing.stronglyMonotone-l-⋆ isOrderedRing:ℤ = {!!}
  isOrderedRing.preservesPositivity-⋅ isOrderedRing:ℤ = {!!}


