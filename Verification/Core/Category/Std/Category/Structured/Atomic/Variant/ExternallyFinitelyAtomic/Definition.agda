
module Verification.Core.Category.Std.Category.Structured.Atomic.Variant.ExternallyFinitelyAtomic.Definition where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Preservation
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Functor.Representable2

--
-- Definition from https://nlab-pages.s3.us-east-2.amazonaws.com/nlab/show/atom
--
-- but changed, currently only asks for finite coproducts to be preserved.
--

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isFiniteCoproductPreserving (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field preserve-isCoproduct : ∀{a b x : ⟨ 𝒞 ⟩} -> isCoproduct a b x -> isCoproduct (⟨ F ⟩ a) (⟨ F ⟩ b) (⟨ F ⟩ x)

  open isFiniteCoproductPreserving public

module _ {C : 𝒰 𝑖} {{_ : isCategory {𝑖₁} C}} (𝑗 : 𝔏 ^ 3) where
  isAtom : (e : C) -> 𝒰 _
  isAtom e = isFiniteCoproductPreserving (ℎ𝑜𝑚ᵒᵖ e)
  -- preservesAllColimits (ℎ𝑜𝑚ᵒᵖ e) 𝑗



