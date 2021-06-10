

module Verification.Conventions.Prelude.Classes.Cast where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes.Anything
open import Verification.Conventions.Prelude.Classes.Structure

--------------------------------------------------------------------
-- ====* Casting between different types

record Cast (A : 𝒰 𝑖) (Pred : A -> 𝒰 𝑘) (B : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗 ⊔ 𝑘) where
  constructor newcast
  field cast : (a : A) -> {{_ : Pred a}} -> B
open Cast {{...}} public

-- #Notation/Rewrite# ¡ = {}
-- ¡_ = cast
infixr 60 ⩚_
⩚_ = cast
`_` = cast

instance
  Cast:A,A : ∀{A : 𝒰 𝑖} -> Cast A IAnything A
  Cast.cast Cast:A,A a = a

instance
  Cast:Structure : ∀{A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} -> Cast A P (Structure P)
  Cast.cast Cast:Structure a = ′ a ′




