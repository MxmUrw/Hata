
module Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteCoproductCategory where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product

open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition


-- record hasCoproductGluing (F : Functor 𝒞 ᵒᵖ)

-- module _ {𝒞 : Category 𝑖} {F : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)}
--          {{_ : hasCoproducts 𝒞}}
--          -- {{_ : ∀{c : ⟨ 𝒞 ⟩} -> hasCoproducts (⟨ F ⟩ c)}}
--   where

--   infixl 80 _⊔-⨊ᵒᵖ_

--   _⊔-⨊ᵒᵖ_ : ⨊ᵒᵖ F -> ⨊ᵒᵖ F -> ⨊ᵒᵖ F
--   _⊔-⨊ᵒᵖ_ a b = (base a ⊔ base b) , {!!}
--   -- ⟨ map π₀ ⟩ (fib a) ⊔ ⟨ map π₁ ⟩ (fib b)

--   -- module _ {a b : ⨊ᵒᵖ F} where
--   --   ι₀-⨊ᵒᵖ : a ⟶ a ⊔-⨊ᵒᵖ b
--   --   ι₀-⨊ᵒᵖ = {!!} , {!!}
--   instance
--     hasCoproducts:⨊ᵒᵖ : hasCoproducts ′(⨊ᵒᵖ F)′
--     hasCoproducts:⨊ᵒᵖ = {!!}

--   instance
--     hasFiniteCoproducts:⨊ᵒᵖ : hasFiniteCoproducts ′(⨊ᵒᵖ F)′
--     hasFiniteCoproducts:⨊ᵒᵖ = {!!}



