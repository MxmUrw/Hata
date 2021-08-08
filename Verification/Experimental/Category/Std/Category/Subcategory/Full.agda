
module Verification.Experimental.Category.Std.Category.Subcategory.Full where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition


-- module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where
module _ (𝒞 : Category 𝑖) where
  record FullSubcategory {X : 𝒰 𝑘} (f : X -> ⟨ 𝒞 ⟩) : 𝒰 𝑘 where
    constructor incl
    field ⟨_⟩ : X
  open FullSubcategory {{...}} public

  macro
    𝐅𝐮𝐥𝐥 : {X : 𝒰 𝑘} (f : X -> ⟨ 𝒞 ⟩) -> SomeStructure
    𝐅𝐮𝐥𝐥 f = #structureOn (FullSubcategory f)


module _ {𝒞 : Category 𝑖} where
  module _ {X : 𝒰 𝑘} {ι : X -> ⟨ 𝒞 ⟩} where


    instance
      isDiscrete:FullSubcategory : {{_ : isDiscrete X}} -> isDiscrete (FullSubcategory 𝒞 ι)
      isDiscrete:FullSubcategory = {!!}

      isSet-Str:FullSubcategory : {{_ : isSet-Str X}} -> isSet-Str (FullSubcategory 𝒞 ι)
      isSet-Str:FullSubcategory = {!!}


    𝒟 = FullSubcategory 𝒞 ι
    FullSubcategoryHom : 𝒟 -> 𝒟 -> 𝒰 _
    -- FullSubcategoryHom = (λ a b -> ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩)
    FullSubcategoryHom = Hom-Base (λ a b -> ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩)

    module _ {a b : 𝒟} where
      _∼-FullSubcategoryHom_ : (f g : FullSubcategoryHom a b) -> 𝒰 _
      _∼-FullSubcategoryHom_ = λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩
      -- instance
      --   isEquivRel:

      isSetoid:FullSubcategoryHom : isSetoid (FullSubcategoryHom a b)
      isSetoid:FullSubcategoryHom = setoid _∼-FullSubcategoryHom_ {!!} {!!} {!!}
        -- isSetoid._∼'_ isSetoid:FullSubcategoryHom = _∼-FullSubcategoryHom_
        -- isSetoid.isEquivRel:∼ isSetoid:FullSubcategoryHom = {!!}

    instance
      isCategory:FullSubcategory : isCategory (FullSubcategory 𝒞 ι)
      isCategory.Hom isCategory:FullSubcategory a b = FullSubcategoryHom a b
      isCategory.isSetoid:Hom isCategory:FullSubcategory = isSetoid:FullSubcategoryHom
      isCategory.id isCategory:FullSubcategory = incl id
      isCategory._◆_ isCategory:FullSubcategory = λ f g -> incl (_◆_ {{of 𝒞}} ⟨ f ⟩ ⟨ g ⟩)
      isCategory.unit-l-◆ isCategory:FullSubcategory = {!!} -- unit-l-◆ {{of 𝒞}}
      isCategory.unit-r-◆ isCategory:FullSubcategory = {!!}
      isCategory.unit-2-◆ isCategory:FullSubcategory = {!!}
      isCategory.assoc-l-◆ isCategory:FullSubcategory = {!!}
      isCategory.assoc-r-◆ isCategory:FullSubcategory = {!!}
      isCategory._◈_ isCategory:FullSubcategory = {!!}


    -- private
    ForgetFull : 𝐅𝐮𝐥𝐥 𝒞 ι -> ⟨ 𝒞 ⟩
    ForgetFull x = ι ⟨ x ⟩

    instance
      Register:ForgetFull = register[ "" ] (ForgetFull)

    instance
      isFunctor:ForgetFull : isFunctor (𝐅𝐮𝐥𝐥 𝒞 ι) 𝒞 (ForgetFull)
      isFunctor:ForgetFull = {!!}



-- instance
--   Register:ForgetFull : ∀{𝒞 : 𝒰 𝑖} {{_ : isCategory 𝑗 𝒞}} {X : 𝒰 𝑘} {ι : X -> 𝒞} -> Register (𝐅𝐮𝐥𝐥 ι -> 𝒞) ""
--   Register:ForgetFull {ι = ι} = register (ForgetFull {ι = ι})







