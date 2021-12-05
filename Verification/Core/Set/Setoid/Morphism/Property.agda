
module Verification.Core.Set.Setoid.Morphism.Property where

open import Verification.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Morphism.Iso.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Set.Setoid.Morphism.Injective
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑖₁} B}} where
  isInjective:byIso : {f : A -> B} {{_ : isSetoidHom ′ A ′ ′ B ′ f}} {{_ : isIso (hom f)}} -> isInjective f
  isInjective:byIso = {!!}


