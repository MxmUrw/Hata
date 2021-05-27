
module Verification.Core.Category.Limit.Specific.Initial where

open import Verification.Conventions hiding (𝟘-elim)
open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Cat

module _ {X : 𝒰 𝑖} {{_ : isCategory X 𝑗}} where
  record isInitial (a : X) : 𝒰 (𝑖 ､ 𝑗) where
    field 𝟘-elim : ∀(b : X) -> a ⟶ b
          expand-𝟘 : ∀{b : X} -> (f : a ⟶ b) -> f ≣ 𝟘-elim b
open isInitial {{...}} public

record hasInitial (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field 𝟘 : ⟨ 𝒞 ⟩
        {{isInitial:𝟘}} : isInitial 𝟘
open hasInitial {{...}} public



