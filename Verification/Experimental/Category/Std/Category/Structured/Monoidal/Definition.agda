
module Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Limit.Specific.Product

-- instance
--   isCategory:× : ∀{𝒞 𝒟 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{_ : isCategory {𝑗} 𝒟}} -> isCategory {𝑗} (𝒞 ×-𝒰 𝒟)
--   isCategory:× = {!!}



module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
  λ₋ : (A -> B -> C) -> (A ×-𝒰 B -> C)
  λ₋ f (a , b) = f a b

record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  constructor monoidal
  field {{isMonoid:this}} : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)

  field {{isFunctor:⋆}} : isFunctor ′(⟨ 𝒞 ⟩ ×-𝒰 ⟨ 𝒞 ⟩)′ 𝒞 (λ₋ _⋆_)
  -- field {{isFunctor:⋆}} : isFunctor {𝑖} {𝑖} (𝒞 × 𝒞) 𝒞 (λ₋ _⋆_)

  -- field map-⊗ : ∀{a b c d : ⟨ 𝒞 ⟩} (f : a ⟶ b) (g : c ⟶ d) -> (a ⋆ c ⟶ b ⋆ d)

  field compat-Monoidal-⋆ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (p : a ≅ b) -> (q : c ≅ d)
                            -> ⟨ p ≀⋆≀ q ⟩ ∼ map (⟨ p ⟩ , ⟨ q ⟩)
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
  unit-r-⊗ = {!!}


  ⨂-𝔽 : ∀{n} -> (𝔽ʳ n -> 𝒞) -> 𝒞
  ⨂-𝔽 = {!!}


module _ {𝑖} where
  instance
    isCategory:MonoidalCategory : isCategory {{!!}} (MonoidalCategory 𝑖)
    isCategory:MonoidalCategory = {!!}

macro
  𝐌𝐨𝐧𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
  𝐌𝐨𝐧𝐂𝐚𝐭 𝑖 = #structureOn (MonoidalCategory 𝑖)

