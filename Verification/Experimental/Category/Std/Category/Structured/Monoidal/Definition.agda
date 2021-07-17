
module Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Category.Instance.ProductMonoid
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Iso
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition
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

  myI : ⊤ ⟶ 𝒞
  myI = const ◌ since isFunctor:const

  I⋆ : Functor 𝒞 𝒞
  I⋆ = ⧼ intro-⊤ ◆ myI , id ⧽ ◆ ′(λ₋ _⋆_)′

  field {{isNaturalIso:unit-l-⋆}} : isNaturalIso I⋆ id unit-l-⋆

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


module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where
  instance
    isMonoidal:Lift : {{_ : isMonoidal ′ 𝒞 ′}} -> isMonoidal ′ Lift-Cat {𝑘} 𝒞 ′
    isMonoid._⋆_ (isMonoidal.isMonoid:this isMonoidal:Lift) = λ a b -> lift (lower a ⋆ lower b)
    isMonoid.◌ (isMonoidal.isMonoid:this isMonoidal:Lift) = lift ◌
    isMonoid.unit-l-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid.unit-r-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid.assoc-l-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid.assoc-r-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid._`cong-⋆`_ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoidal.compat-Monoidal-⋆ isMonoidal:Lift p q = {!!}
    isMonoidal.isFunctor:⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:unit-l-⋆ isMonoidal:Lift = {!!}
    -- isMonoidal.map-⊗ isMonoidal:Lift f g = {!!}
