
module Verification.Experimental.Order.DedekindCompletion.Definition3 where

open import Verification.Conventions
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Order.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number
-- and https://ncatlab.org/nlab/show/Dedekind+cut


-- record isSubsetoid' {𝑗 : 𝔏 ^ 2} {A : Setoid 𝑗} (P : ⟨ A ⟩ -> 𝒰 𝑘) : 𝒰 (𝑗 ､ 𝑘) where
record isSubsetoid' {𝑗 : 𝔏 ^ 2} {A} {{_ : Setoid 𝑗 on A}} (P : A -> 𝒰 𝑘) : 𝒰 (𝑗 ､ 𝑘) where
  field transp-Subsetoid' : ∀{a b} -> a ∼ b -> P a -> P b

open isSubsetoid' {{...}} public

Subsetoid' : {𝑗 : 𝔏 ^ 2} (X : Setoid 𝑗) (𝑘 : 𝔏) -> 𝒰 _
Subsetoid' X 𝑘 = (⟨ X ⟩ -> 𝒰 𝑘):& isSubsetoid'

instance
  isEquivRel:⫗' : ∀{𝑖 : 𝔏 ^ 2} {𝑘 : 𝔏} -> ∀{A : Setoid 𝑖} -> isEquivRel (∼-Base (λ (P Q : Subsetoid' A 𝑘) -> ⟨ P ⟩ ⫗ ⟨ Q ⟩))
  isEquivRel.refl isEquivRel:⫗' = incl ((λ x -> x) , (λ x -> x))
  isEquivRel.sym isEquivRel:⫗' (incl (P , Q)) = incl (Q , P)
  isEquivRel._∙_ isEquivRel:⫗' (incl (P₀ , Q₀)) (incl (P₁ , Q₁)) = incl ((λ x -> P₁ (P₀ x)) , (λ x -> Q₀ (Q₁ x)))

instance
  isSetoid:Subsetoid' : ∀{𝑗 : 𝔏 ^ 2} {𝑘 : 𝔏} -> {X : Setoid 𝑗} -> isSetoid _ (Subsetoid' X 𝑘)
  isSetoid._∼'_ isSetoid:Subsetoid' A B = ⟨ A ⟩ ⫗ ⟨ B ⟩
  -- isSetoid.isEquivRel:∼ isSetoid:Subsetoid' = {!!}
  -- isSetoid.myRel isSetoid:Subsetoid A B = ⟨ A ⟩ ⫗ ⟨ B ⟩


module _ {𝑖 : 𝔏 ^ 3} (X : Linearorder 𝑖) (𝑘 : 𝔏) where

  record isCut (L U : Subsetoid' ′ ⟨ X ⟩ ′ 𝑘) : 𝒰 (𝑖 ､ 𝑘) where
    constructor iscut
    field inhabited-⩘ : ⦋ ⟨ L ⟩ ⦌
    field inhabited-⩗ : ⦋ ⟨ U ⟩ ⦌
    field open-⩘ : ∀{a : ⟨ X ⟩} -> ⟨ L ⟩ a -> ∑ λ (b : ⦋ ⟨ L ⟩ ⦌) -> a < ⟨ b ⟩
    field open-⩗ : ∀{b : ⟨ X ⟩} -> ⟨ U ⟩ b -> ∑ λ (a : ⦋ ⟨ U ⟩ ⦌) -> ⟨ a ⟩ < b
    field compare-Cut : ∀{a b : ⟨ X ⟩} -> a < b -> ⟨ L ⟩ a +-𝒰 ⟨ U ⟩ b
    field by-⩘⩗-< : ∀{a b : ⟨ X ⟩} -> ⟨ L ⟩ a -> ⟨ U ⟩ b -> a < b

  open isCut {{...}} public

  record Cut : 𝒰 (((𝑖 .fst) ⁺) ⊔ 𝑖 ⌄ 1 ⊔ 𝑖 ⌄ 2 ⊔ (𝑘 ⁺)) where
    constructor _,_
    field ⩘ : Subsetoid' ′ ⟨ X ⟩ ′ 𝑘
    field ⩗ : Subsetoid' ′ ⟨ X ⟩ ′ 𝑘
    field {{isCutProof}} : isCut ⩘ ⩗

  open Cut public



module _ {𝑖 : 𝔏 ^ 3} {X : Linearorder 𝑖} {𝑘 : 𝔏} where
  _<L_ : ⟨ X ⟩ -> Cut X 𝑘 -> 𝒰 _
  _<L_ a (L , U) = ⟨ L ⟩ a

  _U<_ : Cut X 𝑘 -> ⟨ X ⟩ -> 𝒰 _
  _U<_ (L , U) b = ⟨ U ⟩ b

  infix 40 _U<_ _<L_ _<-Cut_

  _<-Cut_ : Cut X 𝑘 -> Cut X 𝑘 -> 𝒰 _
  _<-Cut_ x y = ∑ λ a -> (x U< a ×-𝒰 a <L y)

  instance
    isSetoid:Cut : isSetoid _ (Cut X 𝑘)
    isSetoid._∼'_ isSetoid:Cut (L₀ , U₀) (L₁ , U₁) = (L₀ ∼ L₁) ×-𝒰 (U₀ ∼ U₁)
    isEquivRel.refl (isSetoid.isEquivRel:∼ isSetoid:Cut) = incl (refl , refl)
    isEquivRel.sym (isSetoid.isEquivRel:∼ isSetoid:Cut) (incl (p , q)) = incl (sym p , sym q)
    isEquivRel._∙_ (isSetoid.isEquivRel:∼ isSetoid:Cut) (incl (p0 , q0)) (incl (p1 , q1)) = incl (p0 ∙ p1 , q0 ∙ q1)


  disjoint-⩘⩗ : ∀{⩘a ⩗a} -> {{_ : isCut X 𝑘 ⩘a ⩗a}} -> ∀{x} -> ⟨ ⩘a ⟩ x -> ⟨ ⩗a ⟩ x -> 𝟘-𝒰
  disjoint-⩘⩗ p q = irrefl-< (by-⩘⩗-< p q)

  closed-⩘ : ∀{⩘a ⩗a} -> {{_ : isCut X 𝑘 ⩘a ⩗a}} -> ∀{x y} -> (x < y) -> ⟨ ⩘a ⟩ y -> ⟨ ⩘a ⟩ x
  closed-⩘ {⩘a} {⩗a} {x} {y} x<y y-⩘a = case compare-Cut x<y of
                   (λ (p : ⟨ ⩘a ⟩ x) -> p)
                   (λ (p : ⟨ ⩗a ⟩ y) -> 𝟘-rec (disjoint-⩘⩗ y-⩘a p))

  closed-⩗ : ∀{⩘a ⩗a} -> {{_ : isCut X 𝑘 ⩘a ⩗a}} -> ∀{x y} -> (x < y) -> ⟨ ⩗a ⟩ x -> ⟨ ⩗a ⟩ y
  closed-⩗ {⩘a} {⩗a} {x} {y} x<y x-⩗a = case compare-Cut x<y of
                   (λ (p : ⟨ ⩘a ⟩ x) -> 𝟘-rec (disjoint-⩘⩗ p x-⩗a))
                   (λ (p : ⟨ ⩗a ⟩ y) -> p)

{-
{-
-}

-}
