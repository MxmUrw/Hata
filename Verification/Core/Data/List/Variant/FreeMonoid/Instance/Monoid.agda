
module Verification.Core.Data.List.Variant.FreeMonoid.Instance.Monoid where

open import Verification.Core.Conventions hiding (ℕ)

open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.FreeMonoid.Definition
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Setoid


module _ {A : 𝒰 𝑖} where
  instance
    isMonoid:⋆List : isMonoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isMonoid:⋆List = record
      { _⋆_        = _⋆-⧜_
      ; ◌          = ◌-⧜
      ; unit-l-⋆   = incl unit-l-⋆-⧜
      ; unit-r-⋆   = incl unit-r-⋆-⧜
      ; assoc-l-⋆  = incl assoc-l-⋆-⧜
      ; _≀⋆≀_      = cong-⋆-⧜
      }

