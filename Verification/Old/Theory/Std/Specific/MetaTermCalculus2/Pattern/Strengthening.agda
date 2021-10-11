
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Strengthening where

open import Verification.Experimental.Conventions hiding (Structure ; _⊔_ ; extend)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Order.Lattice hiding (⊥)
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Opposite.Instance.Monoid
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.MultiRenaming.Definition
open import Verification.Experimental.Data.MultiRenaming.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.MultiRenaming.Shift

open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteCoproductCategory

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Factorization


-- So, we claim that we can strengthen a pattern term to only claim to use the exact variables
-- which it does use.


module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where
  freeVars : ∀{J : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {i : (Jdg₂ ⟨ K ⟩)} -> (t : J ⊩ᶠ-pat i) -> 人List (Jdg₂ ⟨ K ⟩)
  freeVars = {!!}








