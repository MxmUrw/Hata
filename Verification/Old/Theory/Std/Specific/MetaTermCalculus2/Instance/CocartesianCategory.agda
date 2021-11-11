


module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Instance.CocartesianCategory where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.As.Monoid
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Cartesian
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Instance.Category
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Instance.PrincipalFamilyCat

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



