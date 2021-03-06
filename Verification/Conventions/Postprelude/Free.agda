
module Verification.Conventions.Postprelude.Free where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta2.Macros
open import Verification.Conventions.Meta.Universe
-- open import Verification.Conventions.Prelude.Data.StrictId


record hasFree (A : π° π) (B : π° π) : π° (π ο½€ π) where
  field ππππα΅ : A -> B

open hasFree {{...}} public

macro
  ππππ : β{A : π° π} {B : π° π} {{_ : hasFree A B}} -> SomeStructure
  ππππ = #structureOn ππππα΅

  π₯ππΎπΎ : β{A : π° π} {B : π° π} {{_ : hasFree A B}} -> A -> SomeStructure
  π₯ππΎπΎ a = #structureOn (ππππ a)




