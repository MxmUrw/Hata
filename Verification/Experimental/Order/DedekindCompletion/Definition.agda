
module Verification.Experimental.Order.DedekindCompletion.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition

open import Verification.Experimental.Algebra.Setoid
open import Verification.Experimental.Order.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number
-- and https://ncatlab.org/nlab/show/Dedekind+cut



module _ {𝑖 : 𝔏 ^ 3} (X : Linearorder 𝑖) where

  record isCut (L U : Subsetoid ′ ⟨ X ⟩ ′) : 𝒰 𝑖 where
    constructor iscut
    field inhabited-⩘ : ⦋ ⟨ L ⟩ ⦌
    field inhabited-⩗ : ⦋ ⟨ U ⟩ ⦌
    field open-⩘ : ∀{a : ⟨ X ⟩} -> ⟨ L ⟩ a -> ∑ λ (b : ⦋ ⟨ L ⟩ ⦌) -> a < ⟨ b ⟩
    field open-⩗ : ∀{b : ⟨ X ⟩} -> ⟨ U ⟩ b -> ∑ λ (a : ⦋ ⟨ U ⟩ ⦌) -> ⟨ a ⟩ < b
    field compare-Cut : ∀{a b : ⟨ X ⟩} -> a < b -> ⟨ L ⟩ a +-𝒰 ⟨ U ⟩ b
    field by-⩘⩗-< : ∀{a b : ⟨ X ⟩} -> ⟨ L ⟩ a -> ⟨ U ⟩ b -> a < b

  open isCut {{...}} public

  record Cut : 𝒰 (((𝑖 .fst) ⁺) ⊔ 𝑖 ⌄ 1 ⊔ 𝑖 ⌄ 2) where
    constructor _,_
    field ⩘ : Subsetoid ′ ⟨ X ⟩ ′
    field ⩗ : Subsetoid ′ ⟨ X ⟩ ′
    field {{isCutProof}} : isCut ⩘ ⩗

  open Cut public


module _ {𝑖 : 𝔏 ^ 3} {X : Linearorder 𝑖} where
  _<L_ : ⟨ X ⟩ -> Cut X -> 𝒰 _
  _<L_ a (L , U) = ⟨ L ⟩ a

  _U<_ : Cut X -> ⟨ X ⟩ -> 𝒰 _
  _U<_ (L , U) b = ⟨ U ⟩ b

  infix 40 _U<_ _<L_ _<-Cut_

  _<-Cut_ : Cut X -> Cut X -> 𝒰 _
  _<-Cut_ x y = ∑ λ a -> (x U< a ×-𝒰 a <L y)

  instance
    isSetoid:Cut : isSetoid _ (Cut X)
    isSetoid.myRel isSetoid:Cut (L₀ , U₀) (L₁ , U₁) = (L₀ ∼ L₁) ×-𝒰 (U₀ ∼ U₁)
    isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Cut) = incl (refl , refl)
    isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Cut) (incl (p , q)) = incl (sym p , sym q)
    isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Cut) (incl (p0 , q0)) (incl (p1 , q1)) = incl (p0 ∙ p1 , q0 ∙ q1)


  disjoint-⩘⩗ : ∀{⩘a ⩗a} -> {{_ : isCut X ⩘a ⩗a}} -> ∀{x} -> ⟨ ⩘a ⟩ x -> ⟨ ⩗a ⟩ x -> 𝟘-𝒰
  disjoint-⩘⩗ p q = irrefl-< (by-⩘⩗-< p q)

  closed-⩘ : ∀{⩘a ⩗a} -> {{_ : isCut X ⩘a ⩗a}} -> ∀{x y} -> (x < y) -> ⟨ ⩘a ⟩ y -> ⟨ ⩘a ⟩ x
  closed-⩘ {⩘a} {⩗a} {x} {y} x<y y-⩘a = case compare-Cut x<y of
                   (λ (p : ⟨ ⩘a ⟩ x) -> p)
                   (λ (p : ⟨ ⩗a ⟩ y) -> 𝟘-rec (disjoint-⩘⩗ y-⩘a p))

  closed-⩗ : ∀{⩘a ⩗a} -> {{_ : isCut X ⩘a ⩗a}} -> ∀{x y} -> (x < y) -> ⟨ ⩗a ⟩ x -> ⟨ ⩗a ⟩ y
  closed-⩗ {⩘a} {⩗a} {x} {y} x<y x-⩗a = case compare-Cut x<y of
                   (λ (p : ⟨ ⩘a ⟩ x) -> 𝟘-rec (disjoint-⩘⩗ p x-⩗a))
                   (λ (p : ⟨ ⩗a ⟩ y) -> p)

