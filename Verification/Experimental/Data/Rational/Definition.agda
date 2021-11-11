
module Verification.Core.Data.Rational.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Int.Definition

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Ring.Localization
open import Verification.Core.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Core.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Core.Algebra.Field.Definition
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder

open AbelianMonoidNotation


instance
  hasInclusion:ℕ,ℤ : hasInclusion ℕ ℤ
  hasInclusion:ℕ,ℤ = inclusion pos
  -- record { ιᵘ = pos }


infix 1 existsInU

existsInU : ∀{A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> Prop (ℓ ⊔ ℓ')
existsInU B = ∣ ∑ B ∣

syntax existsInU {A = A} (λ x -> F) = ∃ x ∶ A , F

ℤ₊ₚᵘ : 𝒫 ℤ
ℤ₊ₚᵘ a = ∃ b ∶ ℕ , a ≣ ι (suc b)

macro ℤ₊ₚ = #structureOn ℤ₊ₚᵘ


instance
  isSubsetoid:ℤ₊ₚ : isSubsetoid ℤ₊ₚᵘ
  isSubsetoid:ℤ₊ₚ = record { transp-Subsetoid = lem-1 }
    where
      lem-1 : ∀{a b : ℤ} -> a ∼ b -> a ∈ ℤ₊ₚᵘ -> b ∈ ℤ₊ₚᵘ
      lem-1 (refl-StrId) q = q

pattern refl-≣ = refl-StrId

instance
  isMCS:ℤ₊ₚ : isMCS ℤ ℤ₊ₚ
  isMCS:ℤ₊ₚ = record { closed-⋅ = lem-1 ; closed-⨡ = lem-2 }
    where
      lem-1 : ∀{a b} -> a ∈ ℤ₊ₚᵘ → b ∈ ℤ₊ₚᵘ → (a ⋅-ℤ b) ∈ ℤ₊ₚᵘ
      lem-1 (a' , refl-≣) (b' , refl-≣) = _ , refl

      lem-2 : ⨡ ∈ ℤ₊ₚᵘ
      lem-2 = _ , refl


instance
  hasNotZero-MCS:ℤ₊ₚ : hasNotZero-MCS ℤ₊ₚ
  hasNotZero-MCS:ℤ₊ₚ = record { isNotZero-MCS = lem-1 }
    where
      lem-1 : ∀{a : ℤ} → a ∈ ℤ₊ₚᵘ → a ≁ 0
      lem-1 (a , refl-≣) ()

Rational = Localize ℤ ℤ₊ₚ

macro ℚ = #structureOn Rational

--------------------------------------------------------------------
-- inclusion from ℤ to ℚ

instance
  hasInclusion:ℤ,ℚ : hasInclusion ℤ ℚ
  hasInclusion:ℤ,ℚ = inclusion embed-Localize

instance
  HasFromNat:ℚ : HasFromNat ℚ
  HasFromNat:ℚ = record { Constraint = const 𝟙-𝒰 ; fromNat = λ n -> embed-Localize (pos n) }

instance
  HasFromNeg:ℚ : HasFromNeg ℚ
  HasFromNeg:ℚ = record { Constraint = const 𝟙-𝒰 ; fromNeg = λ n -> embed-Localize (fromNeg (n)) }
  -- record { Constraint = const 𝟙-𝒰 ; fromNat = λ n -> embed-Localize (pos n) }


--------------------------------------------------------------------
-- the equivalences classes of ℚ have representatives with positive
-- denominator

instance
  hasReprHasPositiveDenom:ℚ : hasRepr ℚ hasPositiveDenom
  hasReprHasPositiveDenom:ℚ = record { repr = lem-1 }
    where
      lem-1 : ∀ (a : ℚ) -> Repr hasPositiveDenom a
      lem-1 (a / (pos n ∢ (x , refl-StrId))) = record
        { ⟨_⟩ = (a / pos n ∢ (x , refl-StrId))
        ; represents = refl
        ; hasProperty = incl (λ {(incl (pos Sx≤0)) → ¬-<-zero ⟨ Sx≤0 ⟩})
        }

--------------------------------------------------------------------
-- The linear order on ℚ is unbound


instance
  isUnbound:ℚ : isUnbound ℚ
  isUnbound:ℚ = record
    { getLess    = λ q -> (-1 + q) ∢ lem-1
    ; getGreater = λ q -> (1 + q) ∢ lem-2
    }
    where
      lem-0 : -1 < 0
      lem-0 = incl (incl (λ {(incl ())}))

      lem-0b : 0 < 1
      lem-0b = 0      ⟨ inv-l-⋆ {a = 1} ⟩-∼-<
               -1 + 1 ⟨ stronglyMonotone-l-⋆ lem-0 {1} ⟩-<-∼
               0  + 1 ⟨ unit-l-⋆ ⟩-∼
               1      ∎

      lem-1 : ∀{q} -> (-1 + q) < q
      lem-1 {q} = -1 + q    ⟨ stronglyMonotone-l-⋆ lem-0 {q} ⟩-<-∼
                  0  + q    ⟨ unit-l-⋆ ⟩-∼
                  q         ∎

      lem-2 : ∀{q} -> q < (1 + q)
      lem-2 {q} = q              ⟨ unit-l-⋆ ⁻¹ ⟩-∼-<
                  0 + q          ⟨ stronglyMonotone-l-⋆ lem-0b {q} ⟩-<-∼
                  1 + q          ∎


inv-ℚ : (a : ℚ) -> (a ≁ ◌) -> ℚ
inv-ℚ (a0 / (a1 ∢ _)) p = a1 / (a0 ∢ {!!})

--------------------------------------------------------------------
-- The preorder on ℚ is dense

instance
  isDense:ℚ : isDense ℚ
  isDense:ℚ = record
    { between = λ {a} {b} (a<b) -> (a + b) ⋅ (1 / 2 ∢ (_ , refl)) ∢ {!!}
    }


---------------------------------------------------------------
-- ℚ is a field


⟌-ℚ : (a : ℚ) -> {{not-◌ a}} -> ℚ
⟌-ℚ (a / (b ∢ bp)) {{_}} = b / (a ∢ {!!})

instance
  isField:ℚ : isField ℚ
  isField:ℚ = record
              { ⟌                 = ⟌-ℚ
              ; inv-l-⋅           = {!!}
              ; inv-r-⋅           = {!!}
              ; nontrivial-Field  = {!!}
              }

---------------------------------------------------------------
-- ℚ has abs

abs-ℚ : ℚ -> ℚ
abs-ℚ = {!!}

instance
  Notation-Absolute:ℚ : Notation-Absolute ℚ ℚ
  Notation-Absolute:ℚ = record { ∣_∣ = abs-ℚ }

