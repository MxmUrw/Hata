
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF where

open import Verification.Conventions

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder 
open import Verification.Experimental.Order.Lattice hiding (⊥)

open import Verification.Experimental.Data.List.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem

open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Experimental.Computation.Unification.Monoidic.Instance.hasUnification

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Base
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Main
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Size


module _ {𝑨 : 𝕋× 𝑖} where
  instance
    isPrincipalFamilyCat:𝐂𝐭𝐱-𝕋× : isPrincipalFamilyCat (𝐂𝐭𝐱 𝑨)
    isPrincipalFamilyCat:𝐂𝐭𝐱-𝕋× = record { isBase = isBase-𝕋× ; ∂C = ∂-𝕋× ; isPrincipalC:Base = decide-Base-𝕋× }

  instance
    hasUnification:𝐂𝐭𝐱-𝕋× : hasUnification (𝐂𝐭𝐱 𝑨)
    hasUnification:𝐂𝐭𝐱-𝕋× = hasUnification:byPrincipalFamilyCat (𝐂𝐭𝐱 𝑨)


