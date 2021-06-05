
module Verification.Experimental.Theory.Computation.Unification.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Set.Decidable

record hasUnification (𝒞 : Category 𝑗) : 𝒰 𝑗 where
  field unify : {a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> isDecidable (hasCoequalizer f g)




