
module Verification.Core.Theory.Std.Specific.MetaTermCalculus.MetaSubstitution where

open import Verification.Core.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Std.TypeTheory.Definition
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus.Definition



module _ {σ : MTC.Signature} where
  private
    open MTC.Definitions σ
    open MTC.Signature

    MetaSub : SCtx (MetaJ (MetaKind σ)) -> SCtx (MetaJ (MetaKind σ)) -> 𝒰₀
    MetaSub = {!!}









