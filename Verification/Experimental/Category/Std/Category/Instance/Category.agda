
module Verification.Experimental.Category.Std.Category.Instance.Category where

open import Verification.Experimental.Conventions

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
  _◆-𝐂𝐚𝐭_ : (Functor 𝒞 𝒟) -> Functor 𝒟 𝒢 -> Functor 𝒞 𝒢
  _◆-𝐂𝐚𝐭_ F G = ′ ⟨ F ⟩ ◆-𝒰 ⟨ G ⟩ ′
    where instance
            isFunctor:◆ : isFunctor 𝒞 𝒢 (⟨ F ⟩ ◆-𝒰 ⟨ G ⟩)
            isFunctor.map isFunctor:◆ f             = map (map {{of F}} f)
            isFunctor.isSetoidHom:map isFunctor:◆   = record { cong-∼ = λ p -> cong-∼ (cong-∼ p) }
            isFunctor.functoriality-id isFunctor:◆  = cong-∼ functoriality-id ∙ functoriality-id
            isFunctor.functoriality-◆ isFunctor:◆   = cong-∼ functoriality-◆ ∙ functoriality-◆


    -- isFunctor:◆ : isFunctor ′ 
  -- id-Functor : Functor 𝒞 𝒞
  -- id-Functor = {!!}

macro
  𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
  𝐂𝐚𝐭 𝑖 = #structureOn (Category 𝑖)


instance
  isCategory:Category : ∀{𝑗 : 𝔏 ^ 3} -> isCategory (Category 𝑗)
  isCategory.Hom isCategory:Category = Functor
  isCategory.isSetoid:Hom (isCategory:Category {𝑗}) = it
  isCategory.id isCategory:Category = id-Cat
  isCategory._◆_ isCategory:Category F G = (F ◆-𝐂𝐚𝐭 G)
  isCategory.unit-l-◆ isCategory:Category = {!!}
  isCategory.unit-r-◆ isCategory:Category = {!!}
  isCategory.unit-2-◆ isCategory:Category = {!!}
  isCategory.assoc-l-◆ isCategory:Category = {!!}
  isCategory.assoc-r-◆ isCategory:Category = {!!}
  isCategory._◈_ isCategory:Category = {!!}

instance
  isSetoid:Category : isSetoid (𝐂𝐚𝐭 𝑖)
  isSetoid:Category = isSetoid:byCategory


