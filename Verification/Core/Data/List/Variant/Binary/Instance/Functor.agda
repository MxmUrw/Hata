
module Verification.Core.Data.List.Variant.Binary.Instance.Functor where

open import Verification.Core.Conventions


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

open import Verification.Core.Data.List.Variant.Binary.Definition


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-⋆List : (A -> B) -> ⋆List A -> ⋆List B
  map-⋆List f (incl x) = incl (f x)
  map-⋆List f (as ⋆-⧜ bs) = map-⋆List f as ⋆-⧜ map-⋆List f bs
  map-⋆List f ◌-⧜ = ◌-⧜


instance
  isFunctor:⋆List : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) ⋆List
  isFunctor.map isFunctor:⋆List = map-⋆List
  isFunctor.isSetoidHom:map isFunctor:⋆List = {!!}
  isFunctor.functoriality-id isFunctor:⋆List = {!!}
  isFunctor.functoriality-◆ isFunctor:⋆List = {!!}

