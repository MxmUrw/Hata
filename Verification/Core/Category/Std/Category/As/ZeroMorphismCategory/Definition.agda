
module Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition

-- ===* Categories with zero morphisms

-- | The algebraic intuition behind the concept of an ideal
--   does suggest a small deviation from the existing approach.
--   The reasoning is as follows: It is slightly inconvenient
--   that the result of the unification algorithm is a sum type.
--   In other words, not all coequalizers exist and the algorithm
--   is a decision process for whether a specific pair of arrows
--   has one or not.
--   The inconvenience lies in the fact that each time a recursive
--   call is done, the result needs to be inspected, and depending
--   on whether a failure was reported or not, to continue likewise.
--   The usual tool of error handling in functional languages using
--   monads (REF Wadler monads) seems not to mesh well with the
--   fact that the algorithm needs to be reasoned about afterwards.
-- | A solution which does fit with the rest is as follows.
--   The computation (and verification thereof) is not actually done in the
--   category of substitutions, instead, we move to a category where every
--   coequalizer exists by construction. Then the goal of the algorithm
--   is merely to compute a coequalizer, and no inconvenient case distinctions
--   have to be done.
-- | Of course, this improvement in the formulation of the algorithm does
--   not come for free. We have to translate the coequalizer computed
--   in such a category back to a unification decision in our original
--   category of substitutions. Furthermore, it actually needs to be shown that
--   this correspondence goes both ways.
--
-- | \medskip
--
-- | A category where all coequalizers exist is easily constructed from the
--   category of substitutions. The only thing which needs to be done is
--   to adjoin a single additional arrow to each hom-set |a ⟶ b|.
--   We call this arrow |0 : a ⟶ b|, and composition of other arrows
--   with it works like multiplication with zero: the result is always |0|.
--   This arrow |0| represents the failure in finding a substitution. And it is almost
--   intuitively clear that this meets the requirements stated above. If our
--   algorithm computes that the best coequalizer of two terms (embedded into
--   this category with adjoined zero morphisms) is failure, then no unification
--   is possible in the original category.
--
-- | For the statement of the algorithm we do not even need the definition
--   of that category, merely an axiomatic characterization.

-- [Definition]
-- | We say that a category |𝒞| is a /category with zero morphisms/ [],
--   if the following data is given:
record isZeroMorphismCategory (𝒞 : Category 𝑖) : 𝒰 𝑖 where

  -- | 1. For each pair of objects of |𝒞| the choice of a specified arrow |pt| between them.
  field pt : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b

  -- | 2. Together with proofs that |pt| is always an absorbing element, thus
  --      acts like one would expect from a "zero".
  field absorb-r-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> f ◆ pt {b} {c} ∼ pt {a} {c}
  field absorb-l-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : b ⟶ c} -> pt {a} {b} ◆ f ∼ pt {a} {c}
open isZeroMorphismCategory {{...}} public

-- #Notation/Rewrite# pt = 0

-- //

-- [Hide]
module _ (𝑖 : 𝔏 ^ 3) where
  ZeroMorphismCategory = (Category 𝑖) :& isZeroMorphismCategory

  macro 𝐙𝐌𝐂𝐚𝐭 = #structureOn ZeroMorphismCategory

-- //



