
module Verification.Core.Computation.Unification.Categorical2.ZeroIdeal where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition


-- ===* The zero ideal
-- | Remember that the ideals we are interested in
--   are formed as "set of arrows which unify |t| and |s|",
--   for two terms |t| and |s|. Now if these terms
--   do not have a unification in the original sense, then
--   they still have a "unifier" in the category of substitutions
--   with adjoined zero morphisms, namely |0| itself.
--   Expressed more formally, we know that |(t ◆ pt) ∼ pt ∼ (s ◆ pt)| always holds.


