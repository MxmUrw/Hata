
module Verification.Experimental.Category.Std.Category.Sized.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Computation.Unification.Definition


record isSizedCategory (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⁺) where
  field {{isDiscrete:this}} : isDiscrete ⟨ 𝒞 ⟩
  field {{isSet-Str:this}} : isSet-Str ⟨ 𝒞 ⟩
  field SizeC : WFT0 (ℓ₀ , ℓ₀)
  field sizeC : {a x : ⟨ 𝒞 ⟩} -> (HomPair a x) -> ⟨ SizeC ⟩
  field SizeO : WFT0 (ℓ₀ , ℓ₀)
  field sizeO : ⟨ 𝒞 ⟩ -> ⟨ SizeO ⟩

open isSizedCategory {{...}} public

SizedCategory : ∀ 𝑖 -> _
SizedCategory 𝑖 = _ :& isSizedCategory {𝑖}


module _ {𝒞 : 𝒰 _} {{_ : SizedCategory 𝑖 on 𝒞}} where
  record hasSizedCoequalizer {a b : 𝒞} (f g : a ⟶ b) : 𝒰 𝑖 where
    constructor _,_
    field hasCoequalizer:this : hasCoequalizer f g
    field sized-Coeq : sizeO ⟨ hasCoequalizer:this ⟩ ⪣ sizeO b

  open hasSizedCoequalizer public


  module _ {a b : 𝒞} (f : HomPair a b) where
    hasSizedCoequalizerDecision : 𝒰 𝑖
    hasSizedCoequalizerDecision = (¬ hasCoequalizerCandidate f) +-𝒰 hasSizedCoequalizer (fst f) (snd f)






