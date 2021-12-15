
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition


-- | Abstractly, first order terms are defined to
--   made up of free variables and function symbols.
--   Each function symbol has a finite number
--   of inputs and a single output. In the many sorted case
--   the inputs and outputs of a symbol carry a type (usually called a sort),
--   and only well-typed compositions are allowed.
--   The available sorts and function symbols for a particular
--   term system are succinctly given in a /signature/.

-- [Definition]
-- | A /signature for many sorted terms/,
--   which we call [..], is given by the following data.
record 𝒯FOSignature (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where

  -- | 1. A type of sorts [..].
  field Sort : 𝒰 𝑖

  -- | 2. A parametrized type of function symbols, here called constructors, [...,]
  --      where |Con αs β| contains function symbols
  --      with input sorts |αs| and output sort |β|.
  field Con : List Sort -> Sort -> 𝒰 𝑖

  -- | 3. Proofs that those sets are discrete,
  --      i.e., have decidable equality.
  field {{isDiscrete:Sort}} : isDiscrete Sort
  field {{isDiscrete:Con}} : ∀{αs α} -> isDiscrete (Con αs α)

open 𝒯FOSignature public

-- #Notation/Rewrite# 𝒯FOSignature = Sig_{FO}
-- //

-- [Remark]
-- | The discreteness of the sort and constructor
--   types is required by unification, since the algorithm needs to
--   compare sorts and constructors when unifying terms. On the other hand,
--   no finiteness assumptions are neccessary.

-- //



-- [Hide]
module _ (𝑖 : 𝔏) where
  macro 𝕋× = #structureOn (𝒯FOSignature 𝑖)
-- //

-- [Hide]
-- | We show that the type of sorts of a signature
--   is a set.
module _ {Σ : 𝒯FOSignature 𝑖} where
  instance
    isSet-Str:Sort : isSet-Str (Sort Σ)
    isSet-Str:Sort = {!!}

-- //


