
module Verification.Experimental.Category.Multi.Graph.Definition where

open import Verification.Conventions
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Set.Finite.ReachableSubsets.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice


record isMultiGraph (𝑗 : 𝔏) (G : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Edgeᵐ : ∀{n : ℕ} -> (𝔽ʳ n -> G) -> G -> 𝒰 𝑗

open isMultiGraph {{...}} public

MultiGraph : (𝑖 : 𝔏 ^ 2) -> _
MultiGraph 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isMultiGraph (𝑖 ⌄ 1)



