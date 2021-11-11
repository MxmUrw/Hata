
module Verification.Core.Order.DedekindCompletion.Instance.Linearorder where

open import Verification.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Rational.Definition

open import Verification.Core.Algebra.Setoid
open import Verification.Core.Order.DedekindCompletion.Definition
open import Verification.Core.Order.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number
-- and https://ncatlab.org/nlab/show/Dedekind+cut


module _ {𝑖 : 𝔏 ^ 3} {X : Linearorder 𝑖} where
  instance
    isLinearorder:Cut : isLinearorder _ ′ Cut X ′
    isLinearorder.my< isLinearorder:Cut = _<-Cut_
    isLinearorder.irrefl-< isLinearorder:Cut {⩘ , ⩗} (incl (x , ⩗x , ⩘x)) = disjoint-⩘⩗ ⩘x ⩗x
      -- let X = by-⩘⩗-< ⩘x ⩗x
      -- in irrefl-< X
    isLinearorder.asym-< isLinearorder:Cut {a⩘ , a⩗} {b⩘ , b⩗}  (incl (x , x-a⩗ , x-b⩘)) (incl (y , y-b⩗ , y-a⩘)) =
      let P₀ : x < y
          P₀ = by-⩘⩗-< x-b⩘ y-b⩗

          P₁ : y < x
          P₁ = by-⩘⩗-< y-a⩘ x-a⩗

      in asym-< P₀ P₁
    isLinearorder.compare-< isLinearorder:Cut {a⩘ , a⩗} {c⩘ , c⩗} (incl (x , x-a⩗ , x-c⩘)) (b⩘ , b⩗) =
      let yp : ∑ λ (y : ⦋ ⟨ a⩗ ⟩ ⦌) -> ⟨ y ⟩ < x
          yp = open-⩗ x-a⩗

          y , P₀ = yp

          P₁ : ⟨ b⩘ ⟩ ⟨ y ⟩ +-𝒰 ⟨ b⩗ ⟩ x
          P₁ = compare-Cut P₀

      in case P₁ of
           (λ p -> left (incl (⟨ y ⟩ , Proof y , p)))
           (λ p -> right (incl (x , p , x-c⩘)))

    isLinearorder.connected-< isLinearorder:Cut {a⩘ , a⩗} {b⩘ , b⩗} a≮b b≮a =
      let P₀ : ⟨ a⩘ ⟩ ⫗ ⟨ b⩘ ⟩
          P₀ = let f : ∀{r} -> ⟨ a⩘ ⟩ r -> ⟨ b⩘ ⟩ r
                   f {r} r-a⩘ =
                     let r₂ , r<r₂ = open-⩘ r-a⩘
                     in case compare-Cut r<r₂ of
                          (λ (q : ⟨ b⩘ ⟩ r)      -> q)
                          (λ (q : ⟨ b⩗ ⟩ ⟨ r₂ ⟩)  -> 𝟘-rec (b≮a (incl (⟨ r₂ ⟩ , q , Proof r₂))))
                   g : ∀{r} -> ⟨ b⩘ ⟩ r -> ⟨ a⩘ ⟩ r
                   g {r} r-b⩘ =
                     let r₂ , r<r₂ = open-⩘ r-b⩘
                     in case compare-Cut r<r₂ of
                          (λ (q : ⟨ a⩘ ⟩ r)      -> q)
                          (λ (q : ⟨ a⩗ ⟩ ⟨ r₂ ⟩)  -> 𝟘-rec (a≮b (incl (⟨ r₂ ⟩ , q , Proof r₂))))
               in f , g

          P₁ : ⟨ a⩗ ⟩ ⫗ ⟨ b⩗ ⟩
          P₁ = let f : ∀{r} -> ⟨ a⩗ ⟩ r -> ⟨ b⩗ ⟩ r
                   f {r} r-a⩗ =
                     let r₂ , r<r₂ = open-⩗ r-a⩗
                     in case compare-Cut r<r₂ of
                          (λ (q : ⟨ b⩘ ⟩ ⟨ r₂ ⟩)  -> 𝟘-rec (a≮b (incl (⟨ r₂ ⟩ , Proof r₂ , q))))
                          (λ (q : ⟨ b⩗ ⟩ r)      -> q)
                   g : ∀{r} -> ⟨ b⩗ ⟩ r -> ⟨ a⩗ ⟩ r
                   g {r} r-b⩗ =
                     let r₂ , r<r₂ = open-⩗ r-b⩗
                     in case compare-Cut r<r₂ of
                          (λ (q : ⟨ a⩘ ⟩ ⟨ r₂ ⟩)  -> 𝟘-rec (b≮a (incl (⟨ r₂ ⟩ , Proof r₂ , q))))
                          (λ (q : ⟨ a⩗ ⟩ r)      -> q)
               in f , g

          P₄ : (a⩘ ∼ b⩘) ×-𝒰 (a⩗ ∼ b⩗)
          P₄ = incl P₀ , incl P₁
      in incl P₄

    isLinearorder.transp-< isLinearorder:Cut {⩘a₀ , ⩗a₀} {⩘a₁ , ⩗a₁} {⩘b₀ , ⩗b₀} {⩘b₁ , ⩗b₁} p q (incl (x , x-⩗a₀ , x-⩘b₀)) =
      let P₀ = ⟨ ⟨ p ⟩ .snd ⟩ .fst
          P₁ = ⟨ ⟨ q ⟩ .fst ⟩ .fst
      in incl (x , P₀ x-⩗a₀ , P₁ x-⩘b₀)




