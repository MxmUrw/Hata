
module Verification.Experimental.Category.Std.Morphism.Mono.Subcategory.Instance.FiniteCoproductCategory where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.Mono.Definition
open import Verification.Experimental.Category.Std.Morphism.Mono.Subcategory.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where


  _⊔-𝐒𝐮𝐛ₘₒₙₒ_ : (a b : 𝐒𝐮𝐛ₘₒₙₒ 𝒞) -> 𝐒𝐮𝐛ₘₒₙₒ 𝒞
  _⊔-𝐒𝐮𝐛ₘₒₙₒ_ a b = incl (⟨ a ⟩ ⊔ ⟨ b ⟩)

  module _ {a b : 𝐒𝐮𝐛ₘₒₙₒ 𝒞} where
    isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ : isCoproduct a b (a ⊔-𝐒𝐮𝐛ₘₒₙₒ b)
    isCoproduct.ι₀ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ              = subcathom ι₀ {!!}
    isCoproduct.ι₁ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ              = {!!}
    isCoproduct.⦗ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ ⦘             = {!!}
    isCoproduct.isSetoidHom:⦗⦘ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ  = {!!}
    isCoproduct.reduce-ι₀ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ       = {!!}
    isCoproduct.reduce-ι₁ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ       = {!!}
    isCoproduct.expand-⊔ isCoproduct:⊔-𝐒𝐮𝐛ₘₒₙₒ        = {!!}

  instance
    hasFiniteCoproducts:𝐒𝐮𝐛ₘₒₙₒ : hasFiniteCoproducts (𝐒𝐮𝐛ₘₒₙₒ 𝒞)
    hasFiniteCoproducts:𝐒𝐮𝐛ₘₒₙₒ = {!!}



