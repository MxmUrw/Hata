
module Verification.Core.Data.Language.HindleyMilner.Type.Variant.Direct.Definition where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Natural

-- private variable μs : 人ℕ

-- | Most of the formalization employs rather abstract definitions,
--   as e.g. unification is defined for arbitrary many sorted
--   terms over a signature. Nevertheless it is useful to have
--   a simple and concrete example in mind when illustrating concepts.
--   To that end we give a definition of "simple types", such as
--   could be used for the simply typed lambda calculus,
--   or --- more aligned with the goal of this thesis --- could be used
--   in the definition of type schemes for HM type theory.

-- [Definition]
-- | Let [..] be a list representing variable names.
module _ (μs : 人ℕ) where

  -- |> The type [..] is defined inductively
  --   by the following constructors:

  data Ty-Sim : 𝒰₀ where
    -- | - Type constants for natural numbers and booleans.
    --     We annotate the names with a superscript in order
    --     differentiate them from the actual types in our
    --     Agda metatheory.
    ℕᵗ    : Ty-Sim
    𝔹ᵗ    : Ty-Sim

    -- | - Arrow types.
    _⇒ᵗ_  : Ty-Sim -> Ty-Sim -> Ty-Sim

    -- | - Additionally, type variables may be choosen from
    --     the list of names |μs|.
    var   : μs ∍ tt -> Ty-Sim

-- //



