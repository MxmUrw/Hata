
module Verification.Core.Space.Topological.Basis where

open import Verification.Conventions hiding (Discrete ; ∅ ; Bool ; _and_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice

open import Verification.Core.Space.Topological.Definition

record isTopologicalBasis (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where




