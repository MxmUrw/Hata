
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.MetaSubstitution where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Std.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition



module _ {σ : MTC.Signature} where
  private
    open MTC.Definitions σ
    open MTC.Signature

    MetaSub : SCtx (MetaJ (MetaKind σ)) -> SCtx (MetaJ (MetaKind σ)) -> 𝒰₀
    MetaSub = {!!}









