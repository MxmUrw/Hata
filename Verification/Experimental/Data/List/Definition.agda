
module Verification.Experimental.Data.List.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete

module _ {A : 𝒰 𝑖} where
  instance
    isDiscrete:List : {{_ : isDiscrete A}} -> isDiscrete (List A)
    isDiscrete:List = {!!}

  instance
    isSet-Str:List : {{_ : isSet-Str A}} -> isSet-Str (List A)
    isSet-Str:List = {!!}



