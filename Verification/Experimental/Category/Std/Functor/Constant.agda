
module Verification.Experimental.Category.Std.Functor.Constant where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

--------------------------------------------------------------
-- constant functor
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  isFunctor:const : {x : ⟨ 𝒟 ⟩} -> isFunctor 𝒞 𝒟 (const x)
  isFunctor.map (isFunctor:const {x})              = const id
  isFunctor.isSetoidHom:map (isFunctor:const {x})  = record { cong-∼ = const refl }
  isFunctor.functoriality-id (isFunctor:const {x}) = refl
  isFunctor.functoriality-◆ (isFunctor:const {x})  = unit-2-◆ ⁻¹

  Const : (x : ⟨ 𝒟 ⟩) -> Functor 𝒞 𝒟
  Const x = const x since isFunctor:const



--------------------------------------------------------------
-- definition via structureOn

-- this probably doesn't work because then the instance resolution
-- gets confused with other functors (since `const` is to un-unique as function)
{-
module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  module _ (b : B) where
    𝑐𝑜𝑛𝑠𝑡ᵘ : A -> B
    𝑐𝑜𝑛𝑠𝑡ᵘ _ = b

    macro 𝑐𝑜𝑛𝑠𝑡 = #structureOn 𝑐𝑜𝑛𝑠𝑡ᵘ

  module _ {{_ : isCategory {𝑖₁} A}} {{_ : isCategory {𝑗₁} B}} {b : B} where
    instance
      isFunctor:𝑐𝑜𝑛𝑠𝑡 : isFunctor ′ A ′ ′ B ′ (𝑐𝑜𝑛𝑠𝑡 b)
      isFunctor:𝑐𝑜𝑛𝑠𝑡 = isFunctor:const
-}







