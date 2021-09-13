
module Verification.Experimental.Set.Setoid.Morphism.Property where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Set.Setoid.Morphism.Injective
open import Verification.Experimental.Data.Universe.Everything


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑖₁} B}} where
  isInjective:byIso : {f : A -> B} {{_ : isSetoidHom ′ A ′ ′ B ′ f}} {{_ : isIso (hom f)}} -> isInjective f
  isInjective:byIso = {!!}


