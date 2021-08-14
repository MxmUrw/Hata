
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteCoproductCategory where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.As.Monoid
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory public

open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory public
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory public
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal public

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category

-- open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice hiding (⊥)
-- open import Verification.Experimental.Computation.Unification.Definition
-- open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2
-- open import Verification.Experimental.Computation.Unification.Monoidic.ToCoequalizer
open import Verification.Experimental.Algebra.Monoid.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
-- open import Verification.Experimental.Algebra.MonoidAction.Definition

module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  -- hasFiniteCoproducts:𝐏𝐚𝐭 : hasFiniteCoproducts (𝐏𝐚𝐭 K)
  -- hasFiniteCoproducts:𝐏𝐚𝐭 = it





