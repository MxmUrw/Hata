
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Property.Sized where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Sized.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Epi.Definition

open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Property.Base




module _ {𝒞 : Category 𝑖} {{_ : hasInitial 𝒞}} {{_ : isSizedCategory 𝒞}} where
  module _ {b : ⟨ 𝒞 ⟩} {f g : ⊥ ⟶ b} where

    hasSizedCoequalizer:byInitial : hasSizedCoequalizer f g
    hasSizedCoequalizer:byInitial = hasCoequalizer:byInitial , left (incl refl)


module _ {𝒞 : Category 𝑖} {{_ : isSizedCategory 𝒞}} where
  module _ {a b : ⟨ 𝒞 ⟩} {f : a ⟶ b} where
    hasSizedCoequalizer:byId : hasSizedCoequalizer f f
    hasSizedCoequalizer:byId = hasCoequalizer:byId , left (incl refl)


  module _ {a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} where
    hasSizedCoequalizer:bySym : hasSizedCoequalizer f g -> hasSizedCoequalizer g f
    hasSizedCoequalizer:bySym (p , s) = hasCoequalizer:bySym p , s

