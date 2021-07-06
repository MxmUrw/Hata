
module Verification.Editor.Stack where

open import Verification.Conventions


record Layer 𝑖 : 𝒰 (𝑖 ⁺) where
  field Content : 𝒰 𝑖
  field Coords : 𝒰 𝑖
  -- field f



