
module Verification.Core.Theory.Computation.Refinement.Definition where

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

record isRefinement (𝑖 : 𝔏) (A : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ⁺ ､ 𝑗 ⁺) where
  field 𝒱 : (A -> 𝒰 𝑗) -> 𝒰 (𝑗 ⊔ (𝑖 ⁺))

open isRefinement {{...}} public

Refinement : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Refinement 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isRefinement (𝑖 ⌄ 1)


---------------------------------------------------------------
-- Definition of reductions

module _ (A : Refinement (𝑖 , 𝑗)) (B : Refinement (𝑖 , 𝑘)) where
  record isReduction (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
    field valid : ∀(P : ⟨ A ⟩ -> _) -> 𝒱 P -> 𝒱 (Img f P)

    -- field propMap : ∀(P : ⟨ A ⟩ -> _) -> Property P -> (Property (Img f P))
    -- field solutionMap : ∀(P : ⟨ A ⟩ -> _) -> (PX : Property P) -> ∀ a -> (pa : P a) -> (Solution (P , PX) a pa ↔ Solution (Img f P , propMap P PX) (f a) (a , (pa , refl)))

  Reduction : 𝒰 _
  Reduction = _ :& isReduction

  open isReduction {{...}} public



instance
  isCategory:Refinement : isCategory (_ , ⨆ 𝑖) (Refinement 𝑖)
  isCategory:Refinement =
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


𝐑𝐞𝐟 : ∀ 𝑖 -> SomeStructure
𝐑𝐞𝐟 𝑖 = structureOn (Refinement 𝑖)

