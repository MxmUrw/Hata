

module Verification.Core.Algebra.Basic.Pointed where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Type

--------------------------------------------------------------------
-- === Pointed

record IPointed (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field pt : A
open IPointed {{...}} public

record Pointed 𝑖 : 𝒰 (𝑖 ⁺) where
  constructor pointed
  field ⟨_⟩ : 𝒰 𝑖
        {{Implementation}} : IPointed ⟨_⟩
open Pointed public


