
module Verification.Experimental.Theory.Computation.Problem.As.Refinement where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition
open import Verification.Experimental.Theory.Computation.Refinement.Definition



refine : 𝐏𝐫𝐨𝐛 𝑖 -> 𝐑𝐞𝐟 𝑖
refine Π = {!!}

練 : ∀ {𝑖} -> SomeStructure
練 {𝑖} = structureOn (refine {𝑖})

instance
  isFunctor:練 : isFunctor (𝐏𝐫𝐨𝐛 𝑖) (𝐑𝐞𝐟 𝑖) 練
  isFunctor:練 = {!!}


