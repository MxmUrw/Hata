
module Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Limit.Specific.Product

record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field {{isMonoid:this}} : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)

  field map-⊗ : ∀{a b c d : ⟨ 𝒞 ⟩} (f : a ⟶ b) (g : c ⟶ d) -> (a ⋆ c ⟶ b ⋆ d)
open isMonoidal {{...}} public

MonoidalCategory : ∀ 𝑖 -> 𝒰 _
MonoidalCategory 𝑖 = Category 𝑖 :& isMonoidal


module _ {𝒞 : 𝒰 _} {{_ : MonoidalCategory 𝑖 on 𝒞}} where

  infixl 30 _⊗_

  _⊗_ : 𝒞 -> 𝒞 -> 𝒞
  _⊗_ = _⋆_

  assoc-l-⊗ : ∀{a b c : 𝒞} -> ((a ⊗ b) ⊗ c) ⟶ (a ⊗ (b ⊗ c))
  assoc-l-⊗ = {!!}

  unit-r-⊗ : ∀{a : 𝒞} -> (a ⊗ ◌) ⟶ a
  unit-r-⊗ = ?


  ⨂-𝔽 : ∀{n} -> (𝔽ʳ n -> 𝒞) -> 𝒞
  ⨂-𝔽 = {!!}


module _ {𝑖} where
  instance
    isCategory:MonoidalCategory : isCategory {{!!}} (MonoidalCategory 𝑖)
    isCategory:MonoidalCategory = {!!}

macro
  𝐌𝐨𝐧𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
  𝐌𝐨𝐧𝐂𝐚𝐭 𝑖 = #structureOn (MonoidalCategory 𝑖)

