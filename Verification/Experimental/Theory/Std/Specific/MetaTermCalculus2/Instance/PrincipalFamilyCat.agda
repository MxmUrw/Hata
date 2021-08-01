
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.PrincipalFamilyCat where

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

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamily
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Algebra.MonoidAction.Definition

module _ {K : Kinding 𝑗} {γ : MetaTermCalculus K 𝑖} where
  open MTCDefinitions γ

  instance
    isDiscrete:MTCSubs : isDiscrete (MTCSubs γ)
    isDiscrete:MTCSubs = {!!}

  instance
    isSet-Str:MTCSubs : isSet-Str (MTCSubs γ)
    isSet-Str:MTCSubs = {!!}





  instance
    isPrincipalFamilyCat:MTCSubs : isPrincipalFamilyCat ′ MTCSubs γ ′
    isPrincipalFamilyCat:MTCSubs = {!!}










