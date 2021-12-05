
module Verification.Core.Data.List.Variant.Binary.Misc where

open import Verification.Core.Conventions hiding (ℕ)

open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Contradiction
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition

module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-⋆List : (f : A -> B) -> ⋆List A -> B
  rec-⋆List f (incl x)           = f x
  rec-⋆List f (a ⋆-⧜ b)  = rec-⋆List f a ⋆ rec-⋆List f b
  rec-⋆List f ◌-⧜        = ◌

  instance
    Notation:hasRec:⋆List : Notation:hasRec (A -> B) (⋆List A -> B)
    Notation:hasRec:⋆List = record { rec = rec-⋆List }



-- length of lists
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Instance.Monoid

module _ {A : 𝒰 𝑖} where
  人length : ∀(a : ⋆List A) -> ℕ
  人length = rec-⋆List (const 1)


-----------------------------------------
-- we can decide whether an element is in a list

module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where
  find-first-∍ : ∀ (xs : ⋆List A) -> (x : A) -> isDecidable (xs ∍ x)
  find-first-∍ (incl y) x with x ≟-Str y
  ... | yes refl-≣ = just incl
  ... | no ¬p = left λ {incl → impossible (¬p refl-≣)}
  find-first-∍ (xs ⋆-⧜ ys) x with find-first-∍ xs x | find-first-∍ ys x
  ... | left ¬xs∍x | left ¬ys∍x = left λ { (left-∍ xs∍x) → ¬xs∍x xs∍x
                                         ; (right-∍ ys∍x) → ¬ys∍x ys∍x
                                         }
  ... | left ¬xs∍x | just ys∍x = just (right-∍ ys∍x)
  ... | just xs∍x | Y = right (left-∍ xs∍x)
  find-first-∍ ◌-⧜ x = left λ ()
