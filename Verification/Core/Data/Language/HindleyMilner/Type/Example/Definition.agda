
module Verification.Core.Data.Language.HindleyMilner.Type.Example.Definition where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Data.List.Variant.Base.Definition
open import Verification.Core.Data.List.Variant.Base.Element
open import Verification.Core.Data.List.Variant.Base.Natural


-- [Definition]
-- | The type of monotypes (with one type constant |ℕᵗ| and arrow types |_⇒ᵗ|)
--   is defined as the type [....]
data MonoType : (μs : ♮ℕ) -> 𝒰₀ where
  var   : ∀ {μs x} -> μs ∍♮ x -> MonoType μs
  ℕᵗ    : ∀ {μs} -> MonoType μs
  _⇒ᵗ_  : ∀ {μs} -> MonoType μs -> MonoType μs -> MonoType μs
-- //

-- [Definition]
-- | We can then define polytypes, ie. types quantified over some
--   metavariables as.

-- //



