
module Verification.Experimental.Data.Indexed.Definition where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything


record Indexed (I : 𝒰 𝑖) (A : Category 𝑗) : 𝒰 (𝑖 ⊔ 𝑗 ⌄ 0) where
  constructor indexed
  field ix : I -> ⟨ A ⟩

open Indexed public

module _ (I : 𝒰 𝑖) (A : Category 𝑗) where
  macro
    𝐈𝐱 : SomeStructure
    𝐈𝐱 = #structureOn (Indexed I A)



module _ {I : 𝒰 𝑖} {A : Category 𝑗} where


  module _ (F G : Indexed I A) where
    IndexedHom = ∀{i} -> ix F i ⟶ ix G i

  module _ {F G : Indexed I A} where
    _∼-Indexed_ : (f g : IndexedHom F G) -> 𝒰 _
    _∼-Indexed_ f g = ∀{i} -> f {i} ∼ g {i}

    instance
      isSetoid:IndexedHom : isSetoid (IndexedHom F G)
      isSetoid:IndexedHom = setoid _∼-Indexed_ refl (λ p -> sym p) (λ p q → p ∙ q)

  instance
    isCategory:Indexed : isCategory (Indexed I A)
    isCategory.Hom isCategory:Indexed          = λ F G -> ∀{i} -> ix F i ⟶ ix G i
    isCategory.isSetoid:Hom isCategory:Indexed = it
    isCategory.id isCategory:Indexed           = id
    isCategory._◆_ isCategory:Indexed          = λ f g {i} -> f ◆ g
    isCategory.unit-l-◆ isCategory:Indexed     = unit-l-◆
    isCategory.unit-r-◆ isCategory:Indexed     = unit-r-◆
    isCategory.unit-2-◆ isCategory:Indexed     = unit-2-◆
    isCategory.assoc-l-◆ isCategory:Indexed    = assoc-l-◆
    isCategory.assoc-r-◆ isCategory:Indexed    = assoc-r-◆
    isCategory._◈_ isCategory:Indexed          = {!!}

  instance
    isSetoid:𝐈𝐱 : isSetoid (𝐈𝐱 I A)
    isSetoid:𝐈𝐱 = isSetoid:byCategory





