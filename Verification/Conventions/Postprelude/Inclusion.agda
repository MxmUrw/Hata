
module Verification.Conventions.Postprelude.Inclusion where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta2.Macros
open import Verification.Conventions.Meta.Universe
-- open import Verification.Conventions.Prelude.Data.StrictId


record hasInclusion (A : ๐ฐ ๐) (B : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  constructor inclusion
  field ฮนแต : A -> B

open hasInclusion {{...}} public

macro
  ฮน : โ{A : ๐ฐ ๐} {B : ๐ฐ ๐} {{_ : hasInclusion A B}} -> SomeStructure
  ฮน = #structureOn ฮนแต


