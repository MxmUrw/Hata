
module Verification.Core.Data.List.Variant.Binary.ElementSum.Definition where

open import Verification.Core.Conventions hiding (ℕ)


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition


-- [Hide]
module _ {A : 𝒰 𝑖} where
  record [_]ᶠᵘ (as : ⋆List A) : 𝒰 𝑖 where
    constructor member
    field {getMemberSort} : A
    field getMember : as ∍ getMemberSort

  open [_]ᶠᵘ public

  module _ (as : ⋆List A) where
    macro [_]ᶠ = #structureOn [ as ]ᶠᵘ

  leftᶠᵘ : ∀{as bs} -> [ as ]ᶠ -> [ as ⋆ bs ]ᶠ
  leftᶠᵘ (member a) = member (left-∍ a)

  rightᶠᵘ : ∀{as bs} -> [ bs ]ᶠ -> [ as ⋆ bs ]ᶠ
  rightᶠᵘ (member a) = member (right-∍ a)

  module _ {as bs : ⋆List A} where
    macro leftᶠ  = #structureOn (leftᶠᵘ {as = as} {bs = bs})
    macro rightᶠ = #structureOn (rightᶠᵘ {as = as} {bs = bs})



-- //


