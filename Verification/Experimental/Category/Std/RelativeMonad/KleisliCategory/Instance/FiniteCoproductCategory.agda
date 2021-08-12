
module Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} {𝒟 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒟}} where
  module _ {J : Functor 𝒞 𝒟} {T : RelativeMonad J} {{_ : isFiniteCoproductPreserving J}} where

    infixl 80 _⊔-𝐑𝐞𝐊𝐥𝐬_
    _⊔-𝐑𝐞𝐊𝐥𝐬_ : 𝐑𝐞𝐊𝐥𝐬 T -> 𝐑𝐞𝐊𝐥𝐬 T -> 𝐑𝐞𝐊𝐥𝐬 T
    _⊔-𝐑𝐞𝐊𝐥𝐬_ a b = incl (⟨ a ⟩ ⊔ ⟨ b ⟩)

    ι₀-𝐑𝐞𝐊𝐥𝐬 : ∀{a b : 𝐑𝐞𝐊𝐥𝐬 T} -> a ⟶ a ⊔-𝐑𝐞𝐊𝐥𝐬 b
    ι₀-𝐑𝐞𝐊𝐥𝐬 = incl (map ι₀ ◆ repure)

    ι₁-𝐑𝐞𝐊𝐥𝐬 : ∀{a b : 𝐑𝐞𝐊𝐥𝐬 T} -> b ⟶ a ⊔-𝐑𝐞𝐊𝐥𝐬 b
    ι₁-𝐑𝐞𝐊𝐥𝐬 = incl (map ι₁ ◆ repure)

    ⦗_⦘-𝐑𝐞𝐊𝐥𝐬 : ∀{a b x : 𝐑𝐞𝐊𝐥𝐬 T} -> (f : (a ⟶ x) × (b ⟶ x)) -> a ⊔-𝐑𝐞𝐊𝐥𝐬 b ⟶ x
    ⦗_⦘-𝐑𝐞𝐊𝐥𝐬 (incl f , incl g) = incl (⟨ preserves-⊔ ⟩ ◆ ⦗ f , g ⦘)

    module _ {a b : 𝐑𝐞𝐊𝐥𝐬 T} where
      instance
        isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬 : isCoproduct a b (a ⊔-𝐑𝐞𝐊𝐥𝐬 b)
        isCoproduct.ι₀ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬             = ι₀-𝐑𝐞𝐊𝐥𝐬
        isCoproduct.ι₁ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬             = ι₁-𝐑𝐞𝐊𝐥𝐬
        isCoproduct.⦗ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬 ⦘            = ⦗_⦘-𝐑𝐞𝐊𝐥𝐬
        isCoproduct.isSetoidHom:⦗⦘ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬 = {!!}
        isCoproduct.reduce-ι₀ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬      = {!!}
        isCoproduct.reduce-ι₁ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬      = {!!}
        isCoproduct.expand-⊔ isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬       = {!!}

    instance
      hasInitial:𝐑𝐞𝐊𝐥𝐬 : hasInitial (𝐑𝐞𝐊𝐥𝐬 T)
      hasInitial:𝐑𝐞𝐊𝐥𝐬 = {!!}

      hasCoproducts:𝐑𝐞𝐊𝐥𝐬 : hasCoproducts (𝐑𝐞𝐊𝐥𝐬 T)
      hasCoproducts._⊔_ hasCoproducts:𝐑𝐞𝐊𝐥𝐬            = _⊔-𝐑𝐞𝐊𝐥𝐬_
      hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐑𝐞𝐊𝐥𝐬  = isCoproduct:⊔-𝐑𝐞𝐊𝐥𝐬

    instance
      hasFiniteCoproducts:𝐑𝐞𝐊𝐥𝐬 : hasFiniteCoproducts (𝐑𝐞𝐊𝐥𝐬 T)
      hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:𝐑𝐞𝐊𝐥𝐬     = hasInitial:𝐑𝐞𝐊𝐥𝐬
      hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:𝐑𝐞𝐊𝐥𝐬  = hasCoproducts:𝐑𝐞𝐊𝐥𝐬






