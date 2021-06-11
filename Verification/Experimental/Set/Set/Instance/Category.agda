
module Verification.Experimental.Set.Set.Instance.Category where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition


module _ {P : 𝒰 𝑖 -> 𝒰 𝑗} where
  instance
    isSetoid:Hom-Base-UnderlyingArrow : ∀{A B : 𝒰 𝑖 :& P} -> isSetoid _ (Hom-Base (λ A B -> ⟨ A ⟩ -> ⟨ B ⟩) A B)
    isSetoid:Hom-Base-UnderlyingArrow = setoid R {{lem-1}}
      where R : ∀ f g -> 𝒰 _
            R f g = ∀ a -> ⟨ f ⟩ a ≣ ⟨ g ⟩ a

            lem-1 : isEquivRel (∼-Base R)
            lem-1 = equivRel (incl (λ a -> refl)) (λ p -> incl (λ a -> sym (⟨ p ⟩ a))) (λ p q -> incl (λ a -> ⟨ p ⟩ a ∙ ⟨ q ⟩ a))



instance
  isCategory:Set : isCategory _ (𝐒𝐞𝐭 𝑖)
  isCategory.Hom' isCategory:Set = λ A B -> ⟨ A ⟩ -> ⟨ B ⟩
  isCategory.isSetoid:Hom isCategory:Set = isSetoid:Hom-Base-UnderlyingArrow
  isCategory.id isCategory:Set = incl (λ a -> a)
  isCategory._◆_ isCategory:Set = λ f g -> incl (λ a -> ⟨ g ⟩ (⟨ f ⟩ a))
  isCategory.unit-l-◆ isCategory:Set = incl $ λ a -> refl
  isCategory.unit-r-◆ isCategory:Set = incl $ λ a -> refl
  isCategory.unit-2-◆ isCategory:Set = incl $ λ a -> refl
  isCategory.assoc-l-◆ isCategory:Set = incl $ λ a -> refl
  isCategory.assoc-r-◆ isCategory:Set = incl $ λ a -> refl
  isCategory._◈_ isCategory:Set = {!!}




