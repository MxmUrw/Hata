
module Verification.Experimental.Category.Std.Category.Instance.Category where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Morphism.Iso


all : 𝔏 ^ 3 -> 𝔏
all (i , j , k) = i ⊔ j ⊔ k

module _ {𝒞 : Category 𝑖} where
  id-Cat : Functor 𝒞 𝒞
  id-Cat = ′ id-𝒰 ′
    where instance
            isFunctor:id : isFunctor 𝒞 𝒞 id-𝒰
            isFunctor.map isFunctor:id = id-𝒰
            isFunctor.isSetoidHom:map isFunctor:id = {!!}
            isFunctor.functoriality-id isFunctor:id = {!!}
            isFunctor.functoriality-◆ isFunctor:id = {!!}


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {𝒢 : Category 𝑘} where
  _◆-Cat_ : (Functor 𝒞 𝒟) -> Functor 𝒟 𝒢 -> Functor 𝒞 𝒢
  _◆-Cat_ F G = ′ ⟨ F ⟩ ◆-𝒰 ⟨ G ⟩ ′
    where instance
            isFunctor:◆ : isFunctor 𝒞 𝒢 (⟨ F ⟩ ◆-𝒰 ⟨ G ⟩)
            isFunctor.map isFunctor:◆ f = map (map {{of F}} f)
            isFunctor.isSetoidHom:map isFunctor:◆ = {!!}
            isFunctor.functoriality-id isFunctor:◆ = {!!}
            isFunctor.functoriality-◆ isFunctor:◆ = {!!}


    -- isFunctor:◆ : isFunctor ′ 
  -- id-Functor : Functor 𝒞 𝒞
  -- id-Functor = {!!}

instance
  isCategory:Category : ∀{𝑗 : 𝔏 ^ 3} -> isCategory (_) (Category 𝑗)
  isCategory.Hom' isCategory:Category = Functor
  isCategory.isSetoid:Hom (isCategory:Category {𝑗}) = isSetoid:Hom-Base {{isSetoid:Category}}
  isCategory.id isCategory:Category = incl id-Cat
  isCategory._◆_ isCategory:Category F G = incl (⟨ F ⟩ ◆-Cat ⟨ G ⟩)
  isCategory.unit-l-◆ isCategory:Category = {!!}
  isCategory.unit-r-◆ isCategory:Category = {!!}
  isCategory.unit-2-◆ isCategory:Category = {!!}
  isCategory.assoc-l-◆ isCategory:Category = {!!}
  isCategory.assoc-r-◆ isCategory:Category = {!!}
  isCategory._◈_ isCategory:Category = {!!}

