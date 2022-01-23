
module Verification.Core.Category.Std.Functor.Representable2 where

--
-- NOTE:
--   This is a rewriting of Verification.Core.Category.Std.Functor.Representable,
--   to be merged when more complete.
--

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid


--
-- the hom functors
--
module _ {C : 𝒰 𝑖} {{_ : isCategory {𝑖₁} C}} where
  private
    𝒞 : Category _
    𝒞 = ′ C ′

  module _ (b : C) where
    ℎ𝑜𝑚ᵘ : C -> 𝐒𝐭𝐝 _
    ℎ𝑜𝑚ᵘ a = a ⟶ b

    macro ℎ𝑜𝑚 = #structureOn ℎ𝑜𝑚ᵘ


  module _ {a : C} where
    instance
      isFunctor:ℎ𝑜𝑚 : isFunctor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _) (ℎ𝑜𝑚 a)
      isFunctor:ℎ𝑜𝑚 = {!!}



