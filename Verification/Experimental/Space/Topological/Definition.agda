
module Verification.Experimental.Space.Topological.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition

record isTopological (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field 𝒪 : 𝒰 𝑖
  field openSubset : 𝒪 -> (A -> 𝒰 𝑖)







