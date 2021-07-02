
module Verification.Experimental.Algebra.Field.Definition where

open import Verification.Conventions

open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition


record isField (R : Ring 𝑖) : 𝒰 𝑖 where
  field _⁻¹f : (a : ⟨ R ⟩) -> {{a ≁ ◌}} -> ⟨ R ⟩
  field 


