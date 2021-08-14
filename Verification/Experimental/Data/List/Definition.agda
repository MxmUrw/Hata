
module Verification.Experimental.Data.List.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid

module _ {A : 𝒰 𝑖} where
  instance
    isDiscrete:List : {{_ : isDiscrete A}} -> isDiscrete (List A)
    isDiscrete:List = {!!}



