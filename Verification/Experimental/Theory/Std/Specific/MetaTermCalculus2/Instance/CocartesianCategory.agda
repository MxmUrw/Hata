


module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.CocartesianCategory where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.As.Monoid
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Cartesian
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.Category
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.PrincipalFamilyCat

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


module _ {K : Kinding 𝑖} {γ : MetaTermCalculus K 𝑖} where
  open MTCDefinitions γ

  𝒞 : Category _
  𝒞 = ′ MTCSubs γ ′


  private
    module _ {a b : MTCSubs γ} (f g : a ⟶ b) where


      M : Monoid₀ _
      M = ′ PathMon (′ MTCSubs γ ′) ′

      lem-10 : isPrincipalFamily M _ _ _
      lem-10 = by-PrincipalCat-Principal ′ MTCSubs γ ′

      lem-20 : isPrincipal/⁺-r _ ′(CoeqSolutions (arrow f) (arrow g))′
      lem-20 = isPrincipal:Family M _ _ _ {{lem-10}} _ (just (_ , _ , f , g)) refl-≣

      lem-30 : isDecidable (hasCoequalizer f g)
      lem-30 = by-Principal-Unification.proof f g lem-20

  instance
    hasUnification:MTCSubs : hasUnification ′ MTCSubs γ ′
    hasUnification:MTCSubs = record { unify = lem-30 }



