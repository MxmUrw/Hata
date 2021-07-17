
module Verification.Experimental.Category.Std.Functor.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Data.Universe.Everything


module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  macro 𝐅𝐮𝐧𝐜 = #structureOn (Functor 𝒞 𝒟)

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  id-𝐅𝐮𝐧𝐜 : ∀{F : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> Natural F F
  id-𝐅𝐮𝐧𝐜 {F} = id since natural lem-1
    where
      lem-1 : ∀{x y : ⟨ 𝒞 ⟩} (f : x ⟶ y) -> id ◆ map f ∼ map f ◆ id
      lem-1 f = unit-l-◆ ∙ unit-r-◆ ⁻¹

  _◆-𝐅𝐮𝐧𝐜_ : ∀{F G H : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> Natural F G -> Natural G H -> Natural F H
  _◆-𝐅𝐮𝐧𝐜_ α β = ⟨ α ⟩ ◆ ⟨ β ⟩ since natural lem-1
    where
      lem-1 : ∀{x y : ⟨ 𝒞 ⟩} (f : x ⟶ y) -> (⟨ α ⟩ ◆ ⟨ β ⟩) ◆ map f ∼ map f ◆ (⟨ α ⟩ ◆ ⟨ β ⟩)
      lem-1 f = (⟨ α ⟩ ◆ ⟨ β ⟩) ◆ map f    ⟨ assoc-l-◆ ⟩-∼
                ⟨ α ⟩ ◆ (⟨ β ⟩ ◆ map f)    ⟨ refl ◈ naturality f ⟩-∼
                ⟨ α ⟩ ◆ (map f ◆ ⟨ β ⟩)    ⟨ assoc-r-◆ ⟩-∼
                (⟨ α ⟩ ◆ map f) ◆ ⟨ β ⟩    ⟨ naturality f ◈ refl ⟩-∼
                (map f ◆ ⟨ α ⟩) ◆ ⟨ β ⟩    ⟨ assoc-l-◆ ⟩-∼
                map f ◆ (⟨ α ⟩ ◆ ⟨ β ⟩)    ∎

  instance
    isCategory:Functor : isCategory (𝐅𝐮𝐧𝐜 𝒞 𝒟)
    isCategory.Hom isCategory:Functor = Natural
    isCategory.isSetoid:Hom isCategory:Functor = isSetoid:Natural
    isCategory.id isCategory:Functor           = id-𝐅𝐮𝐧𝐜
    isCategory._◆_ isCategory:Functor          = _◆-𝐅𝐮𝐧𝐜_
    isCategory.unit-l-◆ isCategory:Functor     = unit-l-◆
    isCategory.unit-r-◆ isCategory:Functor     = unit-r-◆
    isCategory.unit-2-◆ isCategory:Functor     = unit-2-◆
    isCategory.assoc-l-◆ isCategory:Functor    = assoc-l-◆
    isCategory.assoc-r-◆ isCategory:Functor    = assoc-r-◆
    isCategory._◈_ isCategory:Functor          = λ p q {x} -> p {x} ◈ q {x}

  instance
    isSetoid:Functor : isSetoid (𝐅𝐮𝐧𝐜 𝒞 𝒟)
    isSetoid:Functor = isSetoid:byCategory



