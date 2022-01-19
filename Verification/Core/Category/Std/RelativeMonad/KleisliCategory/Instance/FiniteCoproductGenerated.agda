
module Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductGenerated where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory

open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Morphism.Iso


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} {𝒟 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒟}} where
  module _ {J : Functor 𝒞 𝒟} {T : RelativeMonad J} {{_ : isFiniteCoproductPreserving J}} where

    module _ {{_ : isFiniteCoproductGenerated ′ ⟨ 𝒞 ⟩ ′}} where
      private
        fcg'Size : ∀(a : 𝐑𝐞𝐊𝐥𝐬 T) -> 人ℕ
        fcg'Size a = fcgSize ⟨ a ⟩

        fcg' : ∀(a : 𝐑𝐞𝐊𝐥𝐬 T) -> 𝐈𝐱 [ fcg'Size a ]ᶠ (𝐑𝐞𝐊𝐥𝐬 T)
        fcg' a = let x = fcg ⟨ a ⟩ in indexed (λ i → incl (x ⌄ i))

        fcg'Iso : ∀(a : 𝐑𝐞𝐊𝐥𝐬 T) -> a ≅ ⨆ᶠ (fcg' a)
        fcg'Iso a = {!!}
          where
            p : ⟨ a ⟩ ≅ ⨆ᶠ (fcg ⟨ a ⟩)
            p = fcgIso ⟨ a ⟩

            f : a ⟶ ⨆ᶠ (fcg' a)
            f = incl {!!}


      instance
        isFiniteCoproductGenerated:𝐑𝐞𝐊𝐥𝐬 : isFiniteCoproductGenerated (𝐑𝐞𝐊𝐥𝐬 T)
        isFiniteCoproductGenerated:𝐑𝐞𝐊𝐥𝐬 = record
          { fcgSize = fcg'Size
          ; fcg = fcg'
          ; fcgIso = fcg'Iso
          }



