
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteColimitCategory where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple

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

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamily
open import Verification.Experimental.Computation.Unification.Monoidic.ToCoequalizer
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer


module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  -- coeq-𝐏𝐚𝐭 : (a b : 𝐏𝐚𝐭 K) -> 𝐏𝐚𝐭 K
  -- coeq-𝐏𝐚𝐭 = {!!}

  instance
    isDiscrete:𝐏𝐚𝐭 : isDiscrete (𝐏𝐚𝐭 K)
    isDiscrete:𝐏𝐚𝐭 = {!!}

  instance
    isSet-Str:𝐏𝐚𝐭 : isSet-Str (𝐏𝐚𝐭 K)
    isSet-Str:𝐏𝐚𝐭 = {!!}

  instance
    isPrincipalFamilyCat:𝐏𝐚𝐭 : isPrincipalFamilyCat (𝐏𝐚𝐭 K)
    isPrincipalFamilyCat:𝐏𝐚𝐭 = {!!}

  private
    module _ {a b : 𝐏𝐚𝐭 K} (f g : a ⟶ b) where

      M : Monoid₀ _
      M = ′ PathMon (𝐏𝐚𝐭 K) ′

      lem-10 : isPrincipalFamily M _ _ _
      lem-10 = by-PrincipalCat-Principal (𝐏𝐚𝐭 K)

      lem-20 : isPrincipal/⁺-r _ ′(CoeqSolutions (arrow f) (arrow g))′
      lem-20 = isPrincipal:Family M _ _ _ {{lem-10}} _ (just (_ , _ , f , g)) refl-≣

      lem-30 : isDecidable (hasCoequalizer f g)
      lem-30 = by-Principal-Unification.proof f g lem-20

  instance
    hasUnification:𝐏𝐚𝐭 : hasUnification (𝐏𝐚𝐭 K)
    hasUnification:𝐏𝐚𝐭 = record { unify = lem-30 }





