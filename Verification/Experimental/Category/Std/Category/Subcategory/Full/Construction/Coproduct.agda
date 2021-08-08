
module Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition


module _ {𝒞 : Category 𝑖} {A : 𝒰 𝑗} {f : A -> ⟨ 𝒞 ⟩} where

  module _ {a b x : 𝐅𝐮𝐥𝐥 𝒞 f} where

    isCoproduct:byFullSubcategory : {{_ : isCoproduct (f ⟨ a ⟩) (f ⟨ b ⟩) (f ⟨ x ⟩)}} -> isCoproduct a b x
    isCoproduct.ι₀ isCoproduct:byFullSubcategory = incl ι₀
    isCoproduct.ι₁ isCoproduct:byFullSubcategory = incl ι₁
    isCoproduct.⦗ isCoproduct:byFullSubcategory ⦘ = λ (f , g) -> incl ⦗ ⟨ f ⟩ , ⟨ g ⟩ ⦘
    isCoproduct.isSetoidHom:⦗⦘ isCoproduct:byFullSubcategory = {!!}
    isCoproduct.reduce-ι₀ isCoproduct:byFullSubcategory = reduce-ι₀
    isCoproduct.reduce-ι₁ isCoproduct:byFullSubcategory = reduce-ι₁
    isCoproduct.expand-⊔ isCoproduct:byFullSubcategory = expand-⊔






