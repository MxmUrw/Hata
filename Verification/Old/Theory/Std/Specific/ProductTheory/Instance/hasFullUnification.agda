
module Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasFullUnification where

open import Verification.Conventions

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Set.Discrete
-- open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.Monoid.Free
-- open import Verification.Core.Data.List.Variant.Binary.Element
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)

-- open import Verification.Core.Data.List.Variant.Unary.Definition
-- open import Verification.Core.Data.Nat.Free
-- open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.Indexed.Instance.Monoid
-- open import Verification.Core.Data.FiniteIndexed.Definition
-- open import Verification.Core.Data.Renaming.Definition
-- open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
-- open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.FormalSystem

open import Verification.Core.Computation.Unification.Categorical.PrincipalFamilyCat

open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.PCF.Base
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.PCF.Main
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.PCF.Size





