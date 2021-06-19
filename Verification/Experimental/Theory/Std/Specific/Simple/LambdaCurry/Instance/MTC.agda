
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.MTC where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
-- open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition


module Λ-Curry where

  data Kind : 𝒰₀ where
    Te : Kind

  data TermCon : SimpleCtx Kind → Kind → 𝒰₀ where
    App : TermCon ([] ,, Te ,, Te) Te

  σ : MTC.Signature
  σ = record { MetaKind = Kind ; TermCon = TermCon }






