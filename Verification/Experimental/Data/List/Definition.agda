
module Verification.Core.Data.List.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete

module _ {A : 𝒰 𝑖} where

  module _ {{_ : isDiscrete A}} where
    private
      lem-1 : (a b : List A) → Decision (a ≡-Str b)
      lem-1 [] [] = yes refl-≣
      lem-1 [] (x ∷ b) = no λ ()
      lem-1 (x ∷ a) [] = no λ ()
      lem-1 (x ∷ a) (y ∷ b) with x ≟-Str y | lem-1 a b
      ... | yes p | yes q = yes (cong₂-Str _∷_ p q)
      ... | yes p | no ¬p = no λ {refl-≣ → ¬p refl-≣}
      ... | no ¬p | Y = no λ {refl-≣ → ¬p refl-≣}

    instance
      isDiscrete:List : isDiscrete (List A)
      isDiscrete:List = record { _≟-Str_ = lem-1 }

  instance
    isSet-Str:List : {{_ : isSet-Str A}} -> isSet-Str (List A)
    isSet-Str:List = {!!}



