
module Verification.Core.Data.List.Variant.Binary.Instance.Setoid where

open import Verification.Core.Conventions


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free

open import Verification.Core.Data.List.Variant.Binary.Definition

----------------------------------------------------------
-- The setoid structure on ⋆List


-- [Definition]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- | The relation |∼-⋆List| on |⋆List A| is defined as:
  data _∼-⋆List_ : (a b : ⋆List A) -> 𝒰 𝑖 where
    unit-l-⋆-⧜  : ∀{a} -> ◌-⧜ ⋆-⧜ a ∼-⋆List a
    unit-r-⋆-⧜  : ∀{a} -> a ⋆-⧜ ◌-⧜ ∼-⋆List a
    assoc-l-⋆-⧜ : ∀{a b c} -> (a ⋆-⧜ b) ⋆-⧜ c ∼-⋆List a ⋆-⧜ (b ⋆-⧜ c)
    cong-l-⋆-⧜  : ∀{a b c} -> (a ∼-⋆List b) -> (a ⋆-⧜ c ∼-⋆List b ⋆-⧜ c)
    cong-r-⋆-⧜  : ∀{a b c} -> (b ∼-⋆List c) -> (a ⋆-⧜ b ∼-⋆List a ⋆-⧜ c)

  infix 10 _∼-⋆List_

  instance
    isSetoid:⋆List : isSetoid (⋆List A)
    isSetoid:⋆List = isSetoid:byFree _∼-⋆List_
-- //



