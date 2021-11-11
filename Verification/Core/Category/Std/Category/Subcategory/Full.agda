
module Verification.Core.Category.Std.Category.Subcategory.Full where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Morphism.Mono.Definition


-- module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where
module _ (𝒞 : Category 𝑖) where
  record FullSubcategory {X : 𝒰 𝑘} (f : X -> ⟨ 𝒞 ⟩) : 𝒰 𝑘 where
    constructor incl
    field ⟨_⟩ : X
  open FullSubcategory {{...}} public

  macro
    𝐅𝐮𝐥𝐥 : {X : 𝒰 𝑘} (f : X -> ⟨ 𝒞 ⟩) -> SomeStructure
    𝐅𝐮𝐥𝐥 f = #structureOn (FullSubcategory f)

  macro
    𝑓𝑢𝑙𝑙 : {X : 𝒰 𝑘} (f : X -> ⟨ 𝒞 ⟩) -> SomeStructure
    𝑓𝑢𝑙𝑙 {X = X} f = #structureOn i
      where i : FullSubcategory f -> ⟨ 𝒞 ⟩
            i a = f ⟨ a ⟩


module _ {𝒞' : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞'}} where
  private
    𝒞 : Category _
    𝒞 = ′ 𝒞' ′

  module _ {X : 𝒰 𝑘} {ι : X -> 𝒞'} where


    instance
      isDiscrete:FullSubcategory : {{_ : isDiscrete X}} -> isDiscrete (FullSubcategory 𝒞 ι)
      isDiscrete:FullSubcategory = {!!}

      isSet-Str:FullSubcategory : {{_ : isSet-Str X}} -> isSet-Str (FullSubcategory 𝒞 ι)
      isSet-Str:FullSubcategory = {!!}


    𝒟 = FullSubcategory 𝒞 ι


    record Hom-𝐅𝐮𝐥𝐥 (a b : 𝐅𝐮𝐥𝐥 𝒞 ι) : 𝒰 (𝑗) where
      constructor incl
      field ⟨_⟩ : ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩
    open Hom-𝐅𝐮𝐥𝐥 public

    FullSubcategoryHom : 𝒟 -> 𝒟 -> 𝒰 _
    -- FullSubcategoryHom = (λ a b -> ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩)
    -- FullSubcategoryHom = Hom-Base (λ a b -> ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩)
    FullSubcategoryHom = Hom-𝐅𝐮𝐥𝐥
    -- (λ a b -> ι ⟨ a ⟩ ⟶ ι ⟨ b ⟩)

    -- RelativeKleisliHom : (A B : 𝐅𝐮𝐥𝐥 𝒞 ι) -> 𝒰 _
    -- RelativeKleisliHom = Hom-𝐅𝐮𝐥𝐥

    module _ {A B : 𝐅𝐮𝐥𝐥 𝒞 ι} where
      record ∼-Hom-𝐅𝐮𝐥𝐥 (f g : Hom-𝐅𝐮𝐥𝐥 A B) : 𝒰 (𝑗) where
        constructor incl
        field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩
        -- incl : R a b -> ∼-Hom-𝐅𝐮𝐥𝐥 R a b -- a ∼[ R ] b
      open ∼-Hom-𝐅𝐮𝐥𝐥 public

      -- _∼-RelativeKleisliHom_ : (f g : RelativeKleisliHom A B) -> 𝒰 _
      -- _∼-RelativeKleisliHom_ = ∼-Hom-𝐅𝐮𝐥𝐥

    module _ {a b : 𝒟} where
      _∼-FullSubcategoryHom_ : (f g : FullSubcategoryHom a b) -> 𝒰 _
      _∼-FullSubcategoryHom_ = ∼-Hom-𝐅𝐮𝐥𝐥
      -- λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩


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
      isFunctor:𝑓𝑢𝑙𝑙 : isFunctor (𝐅𝐮𝐥𝐥 𝒞 ι) 𝒞 (𝑓𝑢𝑙𝑙 𝒞 ι)
      isFunctor.map isFunctor:𝑓𝑢𝑙𝑙              = λ f → ⟨ f ⟩
      isFunctor.isSetoidHom:map isFunctor:𝑓𝑢𝑙𝑙  = record { cong-∼ = λ x → ⟨ x ⟩ }
      isFunctor.functoriality-id isFunctor:𝑓𝑢𝑙𝑙 = refl
      isFunctor.functoriality-◆ isFunctor:𝑓𝑢𝑙𝑙  = refl

    instance
      isFaithful:𝑓𝑢𝑙𝑙 : isFaithful (𝑓𝑢𝑙𝑙 𝒞 ι)
      isInjective.cancel-injective (isFaithful.isInjective:map isFaithful:𝑓𝑢𝑙𝑙) x = incl x

    instance
      isFull:𝑓𝑢𝑙𝑙 : isFull (𝑓𝑢𝑙𝑙 𝒞 ι)
      isSurjective.surj (isFull.isSurjective:map isFull:𝑓𝑢𝑙𝑙)     = λ x → incl x
      isSurjective.inv-surj (isFull.isSurjective:map isFull:𝑓𝑢𝑙𝑙) = refl

    instance
      isMonoReflecting:𝑓𝑢𝑙𝑙 : isMonoReflecting (𝑓𝑢𝑙𝑙 𝒞 ι)
      isMonoReflecting:𝑓𝑢𝑙𝑙 = isMonoReflecting:byFaithful

{-
-}

