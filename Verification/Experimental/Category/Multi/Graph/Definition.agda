
module Verification.Core.Category.Multi.Graph.Definition where

open import Verification.Conventions
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Finite.ReachableSubsets.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice


record isMultiGraph (𝑗 : 𝔏) (G : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Edgeᵐ : ∀{n : ℕ} -> (𝔽ʳ n -> G) -> G -> 𝒰 𝑗

open isMultiGraph {{...}} public

MultiGraph : (𝑖 : 𝔏 ^ 2) -> _
MultiGraph 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isMultiGraph (𝑖 ⌄ 1)



