
module Verification.Conventions.Postprelude.Normalization where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta2.Macros
open import Verification.Conventions.Meta.Universe
-- open import Verification.Conventions.Prelude.Data.StrictId


record hasNormalization (A : ๐ฐ ๐) (B : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  constructor normalization
  field โฎแต : A -> B

open hasNormalization {{...}} public

macro
  โฎ : โ{A : ๐ฐ ๐} {B : ๐ฐ ๐} {{_ : hasNormalization A B}} -> SomeStructure
  โฎ = #structureOn โฎแต


