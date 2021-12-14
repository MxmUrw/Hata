
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition


-- | The theory is parametrized by the following data.

-- [Definition]
-- | A signature for multisorted simple terms,
--   which we call [..], is given by the following data.
record 𝒯FOSignature (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where

  -- | 1. A set of sorts [..].
  field Sort : 𝒰 𝑖
  -- | 2. A parametrized set of constructors [..].
  field Con : List Sort -> Sort -> 𝒰 𝑖
  -- | 3. Proofs that those sets are discrete,
  --      i.e., have decidable equality.
  field {{isDiscrete:Sort}} : isDiscrete Sort
  field {{isSet-Str:Sort}} : isSet-Str Sort
  field {{isDiscrete:Con}} : ∀{αs α} -> isDiscrete (Con αs α)

open 𝒯FOSignature public

-- #Notation/Rewrite# 𝒯FOSignature = Sig_{FO}
-- //


-- [Hide]
module _ (𝑖 : 𝔏) where
  macro 𝕋× = #structureOn (𝒯FOSignature 𝑖)
-- //


