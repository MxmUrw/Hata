

module Verification.Core.Set.Finite.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full2
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.HeytingAlgebra
open import Verification.Core.Set.Finite.ReachableSubsets.Definition


instance
  isCategory:Finite : isCategory _ (Finite 𝑖)
  isCategory:Finite = isCategory:FullSubcategory ⟨_⟩



