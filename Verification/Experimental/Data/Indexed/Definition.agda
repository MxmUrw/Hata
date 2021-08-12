
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



module _ {I : 𝒰 𝑖} {A' : 𝒰 𝑗} {{_ : isCategory {𝑘} A'}} where

  private
    A : Category _
    A = ′ A' ′

  module _ (F G : Indexed I A) where
    IndexedHom = ∀ i -> ix F i ⟶ ix G i

  module _ {F G : Indexed I A} where
    _∼-Indexed_ : (f g : IndexedHom F G) -> 𝒰 _
    _∼-Indexed_ f g = ∀ i -> f i ∼ g i

    instance
      isSetoid:IndexedHom : isSetoid (IndexedHom F G)
      isSetoid:IndexedHom = setoid _∼-Indexed_ (λ _ -> refl) (λ p i -> sym (p i)) (λ p q i → p i ∙ q i)

  infixl 50 _◆-𝐈𝐱_
  _◆-𝐈𝐱_ : ∀{a b c : Indexed I A} -> (f : IndexedHom a b) -> (g : IndexedHom b c) -> IndexedHom a c
  _◆-𝐈𝐱_ f g = λ i -> f i ◆ g i

  instance
    isCategory:Indexed : isCategory (Indexed I A)
    isCategory.Hom isCategory:Indexed          = IndexedHom -- λ F G -> ∀{i} -> ix F i ⟶ ix G i
    isCategory.isSetoid:Hom isCategory:Indexed = it
    isCategory.id isCategory:Indexed           = λ i -> id
    isCategory._◆_ isCategory:Indexed          = _◆-𝐈𝐱_ -- λ f g {i} -> f ◆ g
    isCategory.unit-l-◆ isCategory:Indexed     = λ _ -> unit-l-◆
    isCategory.unit-r-◆ isCategory:Indexed     = λ _ -> unit-r-◆
    isCategory.unit-2-◆ isCategory:Indexed     = λ _ -> unit-2-◆
    isCategory.assoc-l-◆ isCategory:Indexed    = λ _ -> assoc-l-◆
    isCategory.assoc-r-◆ isCategory:Indexed    = λ _ -> assoc-r-◆
    isCategory._◈_ isCategory:Indexed          = {!!}

  instance
    isSetoid:𝐈𝐱 : isSetoid (𝐈𝐱 I A)
    isSetoid:𝐈𝐱 = isSetoid:byCategory


-- module _ {I : 𝒰 𝑖} {A : Category 𝑗} where


--   module _ (F G : Indexed I A) where
--     IndexedHom = ∀ i -> ix F i ⟶ ix G i

--   module _ {F G : Indexed I A} where
--     _∼-Indexed_ : (f g : IndexedHom F G) -> 𝒰 _
--     _∼-Indexed_ f g = ∀ i -> f i ∼ g i

--     instance
--       isSetoid:IndexedHom : isSetoid (IndexedHom F G)
--       isSetoid:IndexedHom = setoid _∼-Indexed_ (λ _ -> refl) (λ p i -> sym (p i)) (λ p q i → p i ∙ q i)

--   infixl 50 _◆-𝐈𝐱_
--   _◆-𝐈𝐱_ : ∀{a b c : Indexed I A} -> (f : IndexedHom a b) -> (g : IndexedHom b c) -> IndexedHom a c
--   _◆-𝐈𝐱_ f g = λ i -> f i ◆ g i

--   instance
--     isCategory:Indexed : isCategory (Indexed I A)
--     isCategory.Hom isCategory:Indexed          = IndexedHom -- λ F G -> ∀{i} -> ix F i ⟶ ix G i
--     isCategory.isSetoid:Hom isCategory:Indexed = it
--     isCategory.id isCategory:Indexed           = λ i -> id
--     isCategory._◆_ isCategory:Indexed          = _◆-𝐈𝐱_ -- λ f g {i} -> f ◆ g
--     isCategory.unit-l-◆ isCategory:Indexed     = λ _ -> unit-l-◆
--     isCategory.unit-r-◆ isCategory:Indexed     = λ _ -> unit-r-◆
--     isCategory.unit-2-◆ isCategory:Indexed     = λ _ -> unit-2-◆
--     isCategory.assoc-l-◆ isCategory:Indexed    = λ _ -> assoc-l-◆
--     isCategory.assoc-r-◆ isCategory:Indexed    = λ _ -> assoc-r-◆
--     isCategory._◈_ isCategory:Indexed          = {!!}

--   instance
--     isSetoid:𝐈𝐱 : isSetoid (𝐈𝐱 I A)
--     isSetoid:𝐈𝐱 = isSetoid:byCategory




