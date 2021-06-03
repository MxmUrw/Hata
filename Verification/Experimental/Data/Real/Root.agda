
module Verification.Experimental.Data.Real.Root where

open import Verification.Experimental.Conventions renaming (∑_ to ∑'_)
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Ring.Ordered
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.DedekindCompletion.Definition3
open import Verification.Experimental.Order.DedekindCompletion.Instance.Ring
-- open import Verification.Experimental.Order.DedekindCompletion.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Setoid
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Monoid
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Group
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Ring
open import Verification.Experimental.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Experimental.Data.Real.Definition
open import Verification.Experimental.Data.Rational.Definition

open AbelianMonoidNotation

instance
  HasFromNat:ℝ : HasFromNat ℝ
  HasFromNat:ℝ = record { Constraint = const ⊤-𝒰 ; fromNat = λ n -> return-Cut _ (fromNat n) }

instance
  HasFromNeg:ℝ : HasFromNeg ℝ
  HasFromNeg:ℝ = record { Constraint = const ⊤-𝒰 ; fromNeg = λ n -> return-Cut _ (fromNeg (n)) }


infix 1 sigmaInU

sigmaInU : ∀{A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> 𝒰 (ℓ ⊔ ℓ')
sigmaInU B = ∑' B

syntax sigmaInU {A = A} (λ x -> F) = ∑ x ∶ A , F


module _ {R : 𝒰 _} {{_ : Ring 𝑖 on R}} where




--
-- We show that every real number has a root.
--
-- Part of the idea for how to do the proof is taken from: https://gitlab.com/pbruin/agda-real/-/blob/master/Real/Sqrt.agda
-- (by Peter Bruin)
-- In particular: how to extend the root function to not only work
-- on ℚ but on any element of ℝ

root : (r : ℝ) -> 0 < r -> ℝ
root r rp = ((′ A ′ , ′ B ′) {{{!!}}})
  where A : ℚ -> Prop _
        A x = ∣ x < 0 +-𝒰 (x ⋅ x ∈ ⩘ r) ∣

        B : ℚ -> Prop _
        B x = ∣ (¬ (x < 0) ×-𝒰 (x ⋅ x ∈ ⩗ r)) ∣

        instance
          isSubsetoid':A : isSubsetoid' A
          isSubsetoid':A = {!!}

        instance
          isSubsetoid':B : isSubsetoid' B
          isSubsetoid':B = {!!}

        lem-5 : 1 < 2
        lem-5 = {!!}

        lem-10 : ∀{x q : ℚ} -> (x ² < q) -> ∑ δ ∶ ℚ , ((0 < δ) ∧ ((x + δ)² < q))
        lem-10 {x} {q} p with compare-< lem-5 x
        ... | just x<2 = {!!}
        ... | left 1<x = δ , {!!} , P₂
          where
            P₀ : x ≁ 0
            P₀ = {!!}
            x⁻¹ = (inv-ℚ x P₀)
            1/4 = inv-ℚ 4 {!!}
            1/2 = inv-ℚ 2 {!!}
            1/16x² = inv-ℚ (16 ⋅ x ²) {!!}

            δ' = q + (- x ²)
            δ  = 1/4 ⋅ x⁻¹ ⋅ δ'

            P₂ = (x + δ)²                          ⟨ binomial-2 ⟩-∼-<
                 x ² + (2) ⋅ (x ⋅ δ) + δ ²      ⟨ {!!} ⟩-∼-<
                 x ² + 1/2 ⋅ δ' + 1/16x² ⋅ δ' ²     ⟨ {!!} ⟩-∼-<
                 x ² + δ'                          ⟨ {!!} ⟩-<-∼
                 q                  ∎

                 -- x ² + (1 + 1) ⋅ x ⋅ δ' + δ' ²     ⟨ binomial-2 ⁻¹ ⟩-<-∼
          -- in {!!}

{-
        isCut:AB : isCut ℚ _ ′ A ′ ′ B ′
        isCut:AB = iscut lem-1 lem-2 lem-3 {!!} {!!} {!!}
          where lem-1 : ⦋ A ⦌
                lem-1 = -1 ∢ {!!}
                lem-2 : ⦋ B ⦌
                lem-2 = {!!} ∢ {!!}

                -- lem-3a : 1 < 2
                -- lem-3a = {!!}

                lem-3 : {x : ℚ} → x ∈ A → ∑ b ∶ _ , x < ⟨ b ⟩
                lem-3 {x} (left x₁) = {!!}
                lem-3 {x} (just x⋅x∈⩘r) =
                  let ((q ∢ q∈⩘r) , x⋅x<q) = open-⩘ x⋅x∈⩘r
                      δ , 0<δ , [x+δ]²<q = lem-10 {x} {q} x⋅x<q
                      P₀ : (x + δ)² ∈ ⩘ r
                      P₀ = closed-⩘ [x+δ]²<q q∈⩘r

                      P₁ : x < (x + δ)
                      P₁ = x      ⟨ unit-r-⋆ ⁻¹ ⟩-∼-<
                           x + 0  ⟨ stronglyMonotone-r-⋆ {c = x} 0<δ ⟩-<-∼
                           x + δ  ∎

                  in (((x + δ) ∢ right P₀) , P₁)
-}
                -- with compare-< lem-3a x
                -- ... | left 1<x = (y ∢ y∈A) , {!!}
                --   where δ' = r + (-(x ⋅ x))
                --         y = x + (inv-ℚ x ? ⋅ δ')
                --         y∈A = {!!}
                -- ... | just x = {!!}

{-
root : (q : ℚ) -> 0 < q -> ℝ
root q qp = ((′ A ′ , ′ B ′) {{{!!}}})
  where A : ℚ -> Prop _
        A x = ∣ x < 0 +-𝒰 (x ⋅ x < q) ∣

        B : ℚ -> Prop _
        B x = ∣ ¬ (x < 0 +-𝒰 (x ⋅ x < q)) ∣

        instance
          isSubsetoid':A : isSubsetoid' A
          isSubsetoid':A = {!!}

        instance
          isSubsetoid':B : isSubsetoid' B
          isSubsetoid':B = {!!}

        isCut:AB : isCut ℚ _ ′ A ′ ′ B ′
        isCut:AB = iscut lem-1 lem-2 {!!} {!!} {!!} {!!}
          where lem-1 : ⦋ A ⦌
                lem-1 = -1 ∢ {!!}
                lem-2 : ⦋ B ⦌
                lem-2 = q ∢ {!!}

-}
