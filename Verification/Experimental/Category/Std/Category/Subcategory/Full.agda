
module Verification.Experimental.Category.Std.Category.Subcategory.Full where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Category.Std.Category.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory 𝑗 𝒞}} where
  record FullSubcategory {X : 𝒰 𝑘} (f : X -> 𝒞) : 𝒰 𝑘 where
    constructor incl
    field ⟨_⟩ : X
  open FullSubcategory {{...}} public

  macro
    𝐅𝐮𝐥𝐥 : {X : 𝒰 𝑘} (f : X -> 𝒞) -> SomeStructure
    𝐅𝐮𝐥𝐥 f = #structureOn (FullSubcategory f)


  module _ {X : 𝒰 𝑘} {ι : X -> 𝒞} where


    instance
      isDiscrete:FullSubcategory : {{_ : isDiscrete X}} -> isDiscrete (FullSubcategory ι)
      isDiscrete:FullSubcategory = {!!}

      isSet-Str:FullSubcategory : {{_ : isSet-Str X}} -> isSet-Str (FullSubcategory ι)
      isSet-Str:FullSubcategory = {!!}


    𝒟 = FullSubcategory ι
    FullSubcategoryHom : 𝒟 -> 𝒟 -> 𝒰 _
    FullSubcategoryHom = Hom-Base (λ a b -> ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩)

    module _ {a b : 𝒟} where
      _∼-FullSubcategoryHom_ : (f g : FullSubcategoryHom a b) -> 𝒰 _
      _∼-FullSubcategoryHom_ = λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩
      -- instance
      --   isEquivRel:

      instance
        isSetoid:FullSubcategoryHom : isSetoid _ (FullSubcategoryHom a b)
        isSetoid._∼'_ isSetoid:FullSubcategoryHom = _∼-FullSubcategoryHom_
        isSetoid.isEquivRel:∼ isSetoid:FullSubcategoryHom = {!!}

    instance
      isCategory:FullSubcategory : isCategory _ (FullSubcategory ι)
      isCategory.Hom' isCategory:FullSubcategory a b = ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩
      isCategory.isSetoid:Hom isCategory:FullSubcategory = it
      isCategory.id isCategory:FullSubcategory = incl id
      isCategory._◆_ isCategory:FullSubcategory = {!!}
      isCategory.unit-l-◆ isCategory:FullSubcategory = {!!}
      isCategory.unit-r-◆ isCategory:FullSubcategory = {!!}
      isCategory.unit-2-◆ isCategory:FullSubcategory = {!!}
      isCategory.assoc-l-◆ isCategory:FullSubcategory = {!!}
      isCategory.assoc-r-◆ isCategory:FullSubcategory = {!!}
      isCategory._◈_ isCategory:FullSubcategory = {!!}





