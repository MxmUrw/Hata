
module Verification.Experimental.Category.Std.Limit.Specific.Product where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Category.Std.Category.Definition


record hasProducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where

CartesianCategory : ∀ 𝑖 -> 𝒰 _
CartesianCategory 𝑖 = Category 𝑖 :& hasProducts


module _ {𝒞 : 𝒰 _} {{_ : CartesianCategory 𝑖 on 𝒞}} where

  _⨯_ : 𝒞 -> 𝒞 -> 𝒞
  _⨯_ = {!!}


  ∏-fin : ∀{n} -> (𝔽ʳ n -> 𝒞) -> 𝒞
  ∏-fin = {!!}
