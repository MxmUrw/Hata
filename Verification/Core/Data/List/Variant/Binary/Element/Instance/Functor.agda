
module Verification.Core.Data.List.Variant.FreeMonoid.Element.Instance.Functor where

open import Verification.Core.Conventions hiding (ℕ)


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.FreeMonoid.Definition
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Setoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Monoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Functor
open import Verification.Core.Data.List.Variant.FreeMonoid.Element.Definition


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-∍ : (f : A -> B) -> {as : ⋆List A} {a : A} -> as ∍ a -> map-⋆List f as ∍ f a
  map-∍ f incl = incl
  map-∍ f (right-∍ x) = right-∍ (map-∍ f x)
  map-∍ f (left-∍ x) = left-∍ (map-∍ f x)


