
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Property.Base where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition

open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition



module _ {𝒞 : Category 𝑖} {{_ : hasInitial 𝒞}} where
  module _ {b : ⟨ 𝒞 ⟩} (f g : ⊥ ⟶ b) where

    hasCoequalizer:byInitial : hasCoequalizer f g
    hasCoequalizer:byInitial = b since P
      where
        P : isCoequalizer f g (obj b)
        isCoequalizer.π-Coeq P      = id
        isCoequalizer.∼-Coeq P      = expand-⊥ ∙ expand-⊥ ⁻¹
        isCoequalizer.elim-Coeq P   = λ h x → h
        isCoequalizer.reduce-Coeq P = λ h p → unit-l-◆
        isCoequalizer.expand-Coeq P = λ h p → unit-l-◆ ⁻¹




