
module Verification.Experimental.Set.Decidable where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
-- open import Verification.Experimental.Data.Prop.Everything

isDecidable : ∀(A : 𝒰 𝑖) -> 𝒰 _
isDecidable A = (¬ A) +-𝒰 A

case-Decision_of : ∀{A : 𝒰 𝑖} -> (a : Decision A) -> {P : Decision A -> 𝒰 𝑗}
                   -> (∀ a -> P (no a))
                   -> (∀ a -> P (yes a))
                   -> P a
case-Decision no ¬p of f1 f2 = f1 ¬p
case-Decision yes p of f1 f2 = f2 p
