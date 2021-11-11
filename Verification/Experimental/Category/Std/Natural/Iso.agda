
module Verification.Core.Category.Std.Natural.Iso where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Natural.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isNaturalIso (F G : Functor 𝒞 𝒟) (α : ∀{x : ⟨ 𝒞 ⟩} -> (⟨ F ⟩ x) ≅ (⟨ G ⟩ x)) : 𝒰 (𝑖 ､ 𝑗) where
    constructor naturalIso'
    field {{fstNaturalIso}} : isNatural F G (λ x -> ⟨ α {x} ⟩)
    field {{sndNaturalIso}}  : isNatural G F (λ x -> inverse-◆ (of (α {x})))

  open isNaturalIso {{...}} public

  pattern naturalIso a b = naturalIso' {{natural a}} {{natural b}}



