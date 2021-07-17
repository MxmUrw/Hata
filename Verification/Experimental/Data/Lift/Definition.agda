
module Verification.Experimental.Data.Lift.Definition where

open import Verification.Conventions
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Algebra.Monoid.Definition

record Lift-Cat {j : 𝔏 ^ 3} {i} (A : 𝒰 i) : 𝒰 (i ⊔ (j ⌄ 0)) where
  constructor lift
  field
    lower : A
open Lift-Cat public




record Hom-Lift 𝑘 {𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} (Hom : A -> A -> 𝒰 𝑗) (a : Lift-Cat {𝑘} A) (b : Lift-Cat {𝑘} A) : 𝒰 (𝑗 ⊔ (𝑘 ⌄ 1)) where
  constructor incl
  field ⟨_⟩ : Hom (lower a) (lower b)
  -- incl : R a b -> Hom-Base R a b -- a ∼[ R ] b
open Hom-Lift public




module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where

  module _ {𝑘} {a : Lift-Cat {𝑘} 𝒞} {b : Lift-Cat {𝑘} 𝒞} where
    instance
      isSetoid:Hom-Lift : isSetoid (Hom-Lift 𝑘 (Hom {{𝒞p}}) a b)
      isSetoid:Hom-Lift = setoid
        (λ f g -> Lift {𝑘 ⌄ 2} (⟨ f ⟩ ∼ ⟨ g ⟩))
        (lift refl)
        {!!}
        {!!}
        -- (λ lift sym)
        -- (lift _∙_)

  instance
    isCategory:Lift : ∀{𝑘} -> isCategory (Lift-Cat {𝑘} 𝒞)
    isCategory.Hom (isCategory:Lift {𝑘}) (a) (b) = Hom-Lift 𝑘 (Hom {{𝒞p}}) a b
    isCategory.isSetoid:Hom (isCategory:Lift {𝑘}) = isSetoid:Hom-Lift
    isCategory.id (isCategory:Lift {𝑘}) = incl id
    isCategory._◆_ (isCategory:Lift {𝑘}) f g = incl (⟨ f ⟩ ◆ ⟨ g ⟩)
    isCategory.unit-l-◆ (isCategory:Lift {𝑘}) = lift $ unit-l-◆ {{𝒞p}}
    isCategory.unit-r-◆ (isCategory:Lift {𝑘}) = lift $ unit-r-◆ {{𝒞p}}
    isCategory.unit-2-◆ (isCategory:Lift {𝑘}) = lift $ unit-2-◆ {{𝒞p}}
    isCategory.assoc-l-◆ (isCategory:Lift {𝑘}) = lift $ assoc-l-◆ {{𝒞p}}
    isCategory.assoc-r-◆ (isCategory:Lift {𝑘}) = lift $ assoc-r-◆ {{𝒞p}}
    isCategory._◈_ (isCategory:Lift {𝑘}) = {!!}






