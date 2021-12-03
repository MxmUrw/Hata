
module Verification.Core.Data.List.Variant.Base.Element where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Nat.Free

open import Verification.Core.Data.List.Variant.Base.Definition

-- lists
module _ {A : 𝒰 𝑖} where
  data _∍♮_ : ∀(as : List A) -> (a : A) -> 𝒰 𝑖 where
    incl : ∀{a bs} -> (a ∷ bs) ∍♮ a
    skip : ∀{a b bs} -> bs ∍♮ a ->  (b ∷ bs) ∍♮ a
