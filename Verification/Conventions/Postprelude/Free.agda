
module Verification.Conventions.Postprelude.Free where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta2.Macros
open import Verification.Conventions.Meta.Universe
-- open import Verification.Conventions.Prelude.Data.StrictId


record hasFree (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field 𝑓𝑟𝑒𝑒ᵘ : A -> B

open hasFree {{...}} public

macro
  𝑓𝑟𝑒𝑒 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : hasFree A B}} -> SomeStructure
  𝑓𝑟𝑒𝑒 = #structureOn 𝑓𝑟𝑒𝑒ᵘ

  𝖥𝗋𝖾𝖾 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : hasFree A B}} -> A -> SomeStructure
  𝖥𝗋𝖾𝖾 a = #structureOn (𝑓𝑟𝑒𝑒 a)




