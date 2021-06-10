

module Verification.Conventions.Prelude.Classes.SpecialElements where

open import Verification.Conventions.Proprelude

record Notation-𝟘 (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field `𝟘` : A
open Notation-𝟘 {{...}} public

record Notation-𝟙 (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field `𝟙` : A
open Notation-𝟙 {{...}} public

record Notation-𝟚 (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field `𝟚` : A
open Notation-𝟚 {{...}} public


instance
  Notation-𝟘:𝒰 : Notation-𝟘 (𝒰 𝑖)
  Notation-𝟘.`𝟘` Notation-𝟘:𝒰 = Lift 𝟘-𝒰

instance
  Notation-𝟙:𝒰 : Notation-𝟙 (𝒰 𝑖)
  Notation-𝟙.`𝟙` Notation-𝟙:𝒰 = Lift 𝟙-𝒰




