
module Verification.Core.Data.List.Variant.Binary.Element.Definition where

open import Verification.Core.Conventions hiding (ℕ)


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid

-- the element relation

-- [Definition]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where

  -- |> The element relation [..] is defined similar to
  --    definition (?).
  data _∍_ : ⋆List A -> A -> 𝒰 𝑖 where
    incl : ∀ {x} -> incl x ∍ x
    right-∍ : ∀ {a b x} -> b ∍ x -> (a ⋆ b) ∍ x
    left-∍ : ∀ {a b x} -> a ∍ x -> (a ⋆ b) ∍ x

-- //




-- [Hide]
module _ {A : 𝒰 𝑖} where
  [_]ᶠ : ⋆List A -> 𝒰 𝑖
  [_]ᶠ as = ∑ λ a -> as ∍ a

  leftᶠ : ∀{as bs} -> [ as ]ᶠ -> [ as ⋆ bs ]ᶠ
  leftᶠ (a , p) = a , left-∍ p

  rightᶠ : ∀{as bs} -> [ bs ]ᶠ -> [ as ⋆ bs ]ᶠ
  rightᶠ (a , p) = a , right-∍ p

-- //
