
module Verification.Core.Computation.Unification.Monoidic.Instance.hasUnification where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
-- open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.Monoid.Free
-- open import Verification.Core.Data.List.Variant.Binary.Element
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.Monoid
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.RelativeMonad.Definition
-- open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
-- open import Verification.Core.Category.Std.Category.Subcategory.Definition
-- open import Verification.Core.Category.Std.Morphism.EpiMono
-- open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer

-- open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.Indexed.Instance.Monoid
-- open import Verification.Core.Data.FiniteIndexed.Definition
-- open import Verification.Core.Data.Renaming.Definition
-- open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal

open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
open import Verification.Core.Computation.Unification.Monoidic.ToCoequalizer
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer


module _ (???? : Category (???? , ???? , ????)) {{_ : isSizedCategory ????}} where

  -- coeq-???????????? : (a b : ????) -> ????
  -- coeq-???????????? = {!!}

  -- instance
  --   isDiscrete:???????????? : isDiscrete (????)
  --   isDiscrete:???????????? = {!!}

  -- instance
  --   isSet-Str:???????????? : isSet-Str (????)
  --   isSet-Str:???????????? = {!!}

  module _ {{_ : isPrincipalFamilyCat ???(??? ???? ???)???}} where

    private
      module _ {a b : ??? ???? ???} (f g : a ??? b) where

        M : Monoid??? _
        M = ??? PathMon (????) ???

        lem-10 : isPrincipalFamily M _ _ _
        lem-10 = by-PrincipalCat-Principal (????)

        lem-20 : isPrincipal/???-r _ ???(CoeqSolutions (arrow f) (arrow g))???
        lem-20 = isPrincipal:Family M _ _ _ {{lem-10}} _ (just (_ , _ , f , g)) refl-???

        lem-30 : isDecidable (hasCoequalizer f g)
        lem-30 = by-Principal-Unification.proof f g lem-20

    instance
      hasUnification:byPrincipalFamilyCat : hasUnification (????)
      hasUnification:byPrincipalFamilyCat = record { unify = lem-30 }


