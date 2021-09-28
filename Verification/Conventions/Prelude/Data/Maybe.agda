

module Verification.Conventions.Prelude.Data.Maybe where

open import Verification.Conventions.Proprelude

Maybe : 𝒰 𝑖 -> 𝒰 𝑖
Maybe {𝑖} A = ⊤-𝒰 {𝑖} +-𝒰 A

pattern just a = right a
pattern nothing = left tt

module _ {A B : 𝒰 𝑖} where
  map-Maybe : (f : A -> B) -> Maybe A -> Maybe B
  map-Maybe f (left x) = left x
  map-Maybe f (just x) = just (f x)

