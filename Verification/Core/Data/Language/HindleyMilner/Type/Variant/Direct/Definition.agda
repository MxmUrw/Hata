
module Verification.Core.Data.Language.HindleyMilner.Type.Variant.Direct.Definition where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural


-- [Definition]
-- | The type of monotypes (with two type constants |ℕᵗ|, |𝔹ᵗ| and arrow types |_⇒ᵗ|)
--   is defined as the type [....]
data MonoType : (μs : ♮ℕ) -> 𝒰₀ where
  var   : ∀ {μs x} -> μs ∍♮ x -> MonoType μs
  ℕᵗ    : ∀ {μs} -> MonoType μs
  𝔹ᵗ    : ∀ {μs} -> MonoType μs
  _⇒ᵗ_  : ∀ {μs} -> MonoType μs -> MonoType μs -> MonoType μs
-- //

-- [Definition]
-- | We can then define polytypes, ie. types quantified over some
--   metavariables as.

-- //



