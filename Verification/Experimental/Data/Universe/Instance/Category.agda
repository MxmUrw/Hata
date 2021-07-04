
module Verification.Experimental.Data.Universe.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Definition



instance
  -- isSetoid:Function : ∀{A B : 𝒰 𝑖} -> isSetoid (Hom-Base (λ A B -> A -> B) A B)
  -- isSetoid:Function = setoid (λ f g -> ⟨ f ⟩ ≡ ⟨ g ⟩) 
  isSetoid:Function : ∀{A B : 𝒰 𝑖} -> isSetoid (A -> B)
  isSetoid:Function = isSetoid:byPath


instance
  isCategory:𝒰 : isCategory (𝐓𝐲𝐩𝐞 𝑖)
  isCategory.Hom isCategory:𝒰 A B = A -> B
  isCategory.isSetoid:Hom isCategory:𝒰 = isSetoid:Function
  isCategory.id isCategory:𝒰 = id-𝒰
  isCategory._◆_ isCategory:𝒰 = _◆-𝒰_
  isCategory.unit-l-◆ isCategory:𝒰 = refl
  isCategory.unit-r-◆ isCategory:𝒰 = refl
  isCategory.unit-2-◆ isCategory:𝒰 = refl
  isCategory.assoc-l-◆ isCategory:𝒰 = refl
  isCategory.assoc-r-◆ isCategory:𝒰 = refl
  isCategory._◈_ isCategory:𝒰 p q = λ i -> p i ◆ q i





