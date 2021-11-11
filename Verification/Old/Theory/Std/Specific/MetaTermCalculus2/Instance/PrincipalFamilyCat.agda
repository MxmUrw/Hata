
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Instance.PrincipalFamilyCat where

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

open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Algebra.MonoidAction.Definition

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










