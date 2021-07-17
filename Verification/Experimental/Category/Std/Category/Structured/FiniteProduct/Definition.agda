
module Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product

FiniteProductCategory : ∀ 𝑖 -> 𝒰 _
FiniteProductCategory 𝑖 = Category 𝑖 :& hasFiniteProducts


module _ {𝒞 : 𝒰 _} {{_ : FiniteProductCategory 𝑖 on 𝒞}} where

  _⨯_ : 𝒞 -> 𝒞 -> 𝒞
  _⨯_ = {!!}


  ∏-fin : ∀{n} -> (𝔽ʳ n -> 𝒞) -> 𝒞
  ∏-fin = {!!}







