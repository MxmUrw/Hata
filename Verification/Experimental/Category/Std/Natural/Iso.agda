
module Verification.Experimental.Category.Std.Natural.Iso where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Natural.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isNaturalIso (F G : Functor 𝒞 𝒟) (α : ∀{x : ⟨ 𝒞 ⟩} -> (⟨ F ⟩ x) ≅ (⟨ G ⟩ x)) : 𝒰 (𝑖 ､ 𝑗) where
    field {{natIsoFst}} : isNatural F G (λ {x} -> ⟨ α {x} ⟩)
    field {{natIsoSnd}}  : isNatural G F (λ {x} -> inverse-◆ (of (α {x})))

  open isNaturalIso {{...}} public



