
module Verification.Experimental.Category.Std.Category.Subcategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition


record SubcategoryData (𝒞 : Category 𝑖) {𝑘} (A : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺) where
  constructor subcatdata
  field fst : A -> ⟨ 𝒞 ⟩
  field snd : ∀{a b} -> fst a ⟶ fst b -> 𝒰 𝑘
  -- field isHom-subcat:id : ∀{a} -> isHom-subcat (id {a = subcat a})

open SubcategoryData public

module _ {𝒞 : Category 𝑖} {A : 𝒰 𝑗} where
  record isSubcategory (ι : SubcategoryData 𝒞 {𝑘} A) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    -- field {{isSubsetoid:this}} : ∀{a b} -> isSubsetoid (snd ι {a} {b})
    field closed-◆ : ∀{a b c} -> ∀{f : fst ι a ⟶ fst ι b}
                              -> ∀{g : fst ι b ⟶ fst ι c}
                              -> snd ι f
                              -> snd ι g
                              -> snd ι (f ◆ g)

    field closed-id : ∀{a} -> snd ι (id {a = fst ι a})

  open isSubcategory {{...}} public

  module _ {ι : SubcategoryData 𝒞 {𝑘} A} {{_ : isSubcategory ι}} where
    record SubcategoryHom (a b : A) : 𝒰 (𝑖 ､ 𝑘) where
      constructor subcathom
      field ⟨_⟩ : fst ι a ⟶ fst ι b
      field goodHom : snd ι ⟨_⟩

    open SubcategoryHom public

    module _ {a b : A} where
      record _∼-SubcategoryHom_ (f g : SubcategoryHom a b) : 𝒰 (𝑖 ､ 𝑘) where
        constructor incl
        field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩

      open _∼-SubcategoryHom_ public

      instance
        isSetoid:SubcategoryHom : isSetoid (SubcategoryHom a b)
        isSetoid:SubcategoryHom = setoid _∼-SubcategoryHom_ (incl refl) (λ x → incl (sym ⟨ x ⟩)) (λ p q -> incl (⟨ p ⟩ ∙ ⟨ q ⟩))

        -- isSetoid:SubcategoryHom = setoid (λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩) refl (λ p -> sym p) (λ p q -> p ∙ q)

    id-𝐒𝐮𝐛 : ∀{a : A} -> SubcategoryHom a a
    id-𝐒𝐮𝐛 = subcathom id closed-id

    _◆-𝐒𝐮𝐛_ : ∀{a b c : A} -> (f : SubcategoryHom a b) -> (g : SubcategoryHom b c) -> SubcategoryHom a c
    _◆-𝐒𝐮𝐛_ f g = subcathom (⟨ f ⟩ ◆ ⟨ g ⟩) (closed-◆ (goodHom f) (goodHom g))


    isCategory:bySubcategory : isCategory A
    isCategory.Hom isCategory:bySubcategory           = SubcategoryHom
    isCategory.isSetoid:Hom isCategory:bySubcategory  = isSetoid:SubcategoryHom
    isCategory.id isCategory:bySubcategory            = id-𝐒𝐮𝐛
    isCategory._◆_ isCategory:bySubcategory           = _◆-𝐒𝐮𝐛_
    isCategory.unit-l-◆ isCategory:bySubcategory      = incl $ unit-l-◆
    isCategory.unit-r-◆ isCategory:bySubcategory      = incl $ unit-r-◆
    isCategory.unit-2-◆ isCategory:bySubcategory      = incl $ unit-2-◆
    isCategory.assoc-l-◆ isCategory:bySubcategory     = incl $ assoc-l-◆
    isCategory.assoc-r-◆ isCategory:bySubcategory     = incl $ assoc-r-◆
    isCategory._◈_ isCategory:bySubcategory           = {!!}




