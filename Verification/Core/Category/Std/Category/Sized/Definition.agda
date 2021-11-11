
module Verification.Core.Category.Std.Category.Sized.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Computation.Unification.Definition


record isSizedCategory (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ ℓ₁) where
  -- field {{isDiscrete:this}} : isDiscrete ⟨ 𝒞 ⟩
  -- field {{isSet-Str:this}} : isSet-Str ⟨ 𝒞 ⟩
  field SizeO : WFT0 (ℓ₀ , ℓ₀)
  field sizeO : ⟨ 𝒞 ⟩ -> ⟨ SizeO ⟩

open isSizedCategory {{...}} public

SizedCategory : ∀ 𝑖 -> _
SizedCategory 𝑖 = _ :& isSizedCategory {𝑖}

record isSizedHomPairCategory (𝒞 : SizedCategory 𝑖) : 𝒰 (𝑖 ､ ℓ₁) where
  field SizeC : WFT0 (ℓ₀ , ℓ₀)
  field sizeC : {a x : ⟨ 𝒞 ⟩} -> (HomPair a x) -> ⟨ SizeC ⟩
  field cong-sizeC : ∀{a x : ⟨ 𝒞 ⟩} (f g : HomPair a x) -> f ∼ g -> sizeC f ≣ sizeC g

open isSizedHomPairCategory {{...}} public

SizedHomPairCategory : ∀ 𝑖 -> _
SizedHomPairCategory 𝑖 = _ :& isSizedHomPairCategory {𝑖}


module _ {𝒞 : 𝒰 _} {{_ : SizedCategory 𝑖 on 𝒞}} where
  record hasSizedCoequalizer {a b : 𝒞} (f g : a ⟶ b) : 𝒰 𝑖 where
    constructor _,_
    field hasCoequalizer:this : hasCoequalizer f g
    field sized-Coeq : isId (π₌) +-𝒰 (sizeO ⟨ hasCoequalizer:this ⟩ ≪ sizeO b)

  open hasSizedCoequalizer public


  module _ {a b : 𝒞} (f : HomPair a b) where
    hasSizedCoequalizerDecision : 𝒰 𝑖
    hasSizedCoequalizerDecision = (¬ hasCoequalizerCandidate f) +-𝒰 hasSizedCoequalizer (fst f) (snd f)

  module _ {{d : ∀{a b : 𝒞} {f g : a ⟶ b} -> hasSizedCoequalizerDecision (f , g)}} where

    hasUnification:byHasSizedCoequalizerDecision : hasUnification ′ 𝒞 ′
    hasUnification:byHasSizedCoequalizerDecision = record
      { unify = λ f g → case d {f = f} {g} of
                           left
                           λ (x , _) → right x
      }






