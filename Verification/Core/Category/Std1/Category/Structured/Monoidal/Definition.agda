
module Verification.Core.Category.Std1.Category.Structured.Monoidal.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Std1.Category.Definition


postulate
  ⊤-1𝐂𝐚𝐭 : {𝑖 : 𝔏 ^ 3} -> 1Category 𝑖

  _≅_ : {𝒞 : 𝒰 𝑖} {{_ : is1Category {𝑗} 𝒞}} -> (a b : 𝒞) -> 𝒰 𝑖

record isMonoidal (𝒞 : 1Category 𝑖) : 𝒰 𝑖 where
  field [⊗] : ⟨ 𝒞 ⟩ ×-𝒰 ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field [Id] : ⊤-𝒰 {𝑖 ⌄ 0} -> ⟨ 𝒞 ⟩
  field unit-l-⊗ : ∀{a} -> [⊗] ([Id] tt , a) ≅ a

  field isFunctor:[⊗] : isFunctor (𝒞 ×-1𝐂𝐚𝐭 𝒞) 𝒞 [⊗]





