

module Verification.Experimental.Set.Finite.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full2
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.HeytingAlgebra
open import Verification.Experimental.Set.Finite.ReachableSubsets.Definition


instance
  isCategory:Finite : isCategory _ (Finite 𝑖)
  isCategory:Finite = isCategory:FullSubcategory ⟨_⟩



