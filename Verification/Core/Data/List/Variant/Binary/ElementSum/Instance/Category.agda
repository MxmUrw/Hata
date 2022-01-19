
module Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category where

open import Verification.Core.Conventions hiding (ℕ)


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.Sum.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Discrete
open import Verification.Core.Category.Std.Category.Construction.Coproduct
-- open import Verification.Core.Set.Setoid.As.Category
-- open import Verification.Core.Set.Setoid.Discrete
-- open import Verification.Core.Set.Setoid.Definition

module _ {A : 𝒰 𝑖} where

  instance
    isCategory:[]ᶠ : {as : ⋆List A} -> isCategory [ as ]ᶠ
    isCategory:[]ᶠ = isCategory:byDiscrete


  module _ {as bs : ⋆List A} where
    instance
      isFunctor:leftᶠ : isFunctor [ as ]ᶠ [ as ⋆ bs ]ᶠ leftᶠ
      isFunctor:leftᶠ = isFunctor:byDiscrete

      isFunctor:rightᶠ : isFunctor [ bs ]ᶠ [ as ⋆ bs ]ᶠ rightᶠ
      isFunctor:rightᶠ = isFunctor:byDiscrete


  module _ {as bs : ⋆List A} where
    eval-⋆ᶠᵘ : [ as ⋆ bs ]ᶠ -> [ as ]ᶠ + [ bs ]ᶠ
    eval-⋆ᶠᵘ (member (left-∍ x))   = left (member x)
    eval-⋆ᶠᵘ (member (right-∍ x))  = right (member x)

    macro eval-⋆ᶠ = #structureOn eval-⋆ᶠᵘ

    instance
      isFunctor:eval-⋆ᶠ : isFunctor [ as ⋆ bs ]ᶠ ([ as ]ᶠ +-𝐂𝐚𝐭 [ bs ]ᶠ) eval-⋆ᶠ
      isFunctor:eval-⋆ᶠ = isFunctor:byDiscrete

    eval⁻¹-⋆ᶠᵘ : [ as ]ᶠ + [ bs ]ᶠ -> [ as ⋆ bs ]ᶠ
    eval⁻¹-⋆ᶠᵘ (left (member x)) = member (left-∍ x)
    eval⁻¹-⋆ᶠᵘ (just (member x)) = member (right-∍ x)

    macro eval⁻¹-⋆ᶠ = #structureOn eval⁻¹-⋆ᶠᵘ

    instance
      isFunctor:eval⁻¹-⋆ᶠ : isFunctor ([ as ]ᶠ +-𝐂𝐚𝐭 [ bs ]ᶠ) [ as ⋆ bs ]ᶠ eval⁻¹-⋆ᶠ
      isFunctor:eval⁻¹-⋆ᶠ = {!!}


    -- prop-1 : ∀{as bs : ⋆List A} -> [ as ⋆ bs ]ᶠ 



