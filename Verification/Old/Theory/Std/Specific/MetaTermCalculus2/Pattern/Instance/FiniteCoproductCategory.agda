
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteCoproductCategory where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory public

open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory public
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory public
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal public

open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category

-- open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice hiding (⊥)
-- open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2
-- open import Verification.Core.Computation.Unification.Monoidic.ToCoequalizer
open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
-- open import Verification.Core.Algebra.MonoidAction.Definition

module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  -- hasFiniteCoproducts:𝐏𝐚𝐭 : hasFiniteCoproducts (𝐏𝐚𝐭 K)
  -- hasFiniteCoproducts:𝐏𝐚𝐭 = it





