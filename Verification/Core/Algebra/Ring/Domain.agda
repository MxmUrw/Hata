
module Verification.Core.Algebra.Ring.Domain where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
-- open import Verification.Core.Order.Preorder
-- open import Verification.Core.Order.Totalorder

module _ {𝑖 : 𝔏 ^ 2} where
  record isDomain (R : Ring 𝑖) : 𝒰 𝑖 where
    field domain : ∀{a b : ⟨ R ⟩} -> a ⋅ b ∼ ◌ -> (a ∼ ◌) +-𝒰 (b ∼ ◌)

Domain : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Domain 𝑖 = Ring 𝑖 :& isDomain

module _ {𝑖 : 𝔏 ^ 2} where
  module _ {R : 𝒰 _} {{_ : Domain 𝑖 on R}} where
    cancel-⋅-r : ∀{a b c : R} -> a ⋅ c ∼ b ⋅ c -> (¬ c ∼ ◌) -> a ∼ b
    cancel-⋅-r = {!!}
