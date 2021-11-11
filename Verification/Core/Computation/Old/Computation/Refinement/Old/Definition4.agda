

module Verification.Core.Theory.Computation.Problem.Definition5 where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} (f : A -> B) where
  Img : (A -> 𝒰 𝑘) -> (B -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘))
  Img P b = ∑ λ a -> P a ×-𝒰 (f a ≣ b)

---------------------------------------------------------------
-- Definition of a problem

record isProblem (𝑖 : 𝔏 ^ 2) (A : 𝒰 𝑗) : 𝒰 ((fst 𝑖) ⁺ ⁺ ､ (𝑖 ⌄ 1) ⁺ ､ 𝑗 ⁺) where
  field Property : (A -> 𝒰 𝑗) -> 𝒰 (𝑗 ⊔ (fst 𝑖) ⁺)
  field Solution : ∀(P : ∑ Property) -> (a : A) -> P .fst a -> 𝒰 (𝑖 ⌄ 1)

open isProblem {{...}} public

Problem : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Problem 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isProblem (𝑖 ⌄ 1 , 𝑖 ⌄ 2)


---------------------------------------------------------------
-- Definition of reductions

module _ (A : Problem (𝑖 , 𝑗)) (B : Problem (𝑖 , 𝑘)) where
  record isReduction (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
    field propMap : ∀(P : ⟨ A ⟩ -> _) -> Property P -> (Property (Img f P))
    field solutionMap : ∀(P : ⟨ A ⟩ -> _) -> (PX : Property P) -> ∀ a -> (pa : P a) -> (Solution (P , PX) a pa ↔ Solution (Img f P , propMap P PX) (f a) (a , (pa , refl)))


  Reduction : 𝒰 _
  Reduction = _ :& isReduction

  open isReduction {{...}} public


instance
  isCategory:Problem : isCategory (_ , ⨆ 𝑖) (Problem 𝑖)
  isCategory:Problem =
    record
    { Hom'         = Reduction
    ; isSetoid:Hom = {!!}
    ; id           = {!!}
    ; _◆_          = {!!}
    ; unit-l-◆   = {!!}
    ; unit-r-◆   = {!!}
    ; unit-2-◆   = {!!}
    ; assoc-l-◆  = {!!}
    ; assoc-r-◆  = {!!}
    ; _◈_        = {!!}
    }
