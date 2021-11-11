
module Verification.Old.Core.Category.Instance.Kleisli.Coproducts where

open import Verification.Conventions hiding (𝟘-elim)
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Monad.Definition
open import Verification.Old.Core.Category.Instance.Kleisli.Definition
open import Verification.Old.Core.Category.Limit.Specific.Coproduct
open import Verification.Old.Core.Category.Limit.Specific.Initial

module _ {𝒞 : Category 𝑖} {T : Monad 𝒞} where
  -- [Lemma]
  -- | If |𝒞| has coproducts, i.e., [..], then |𝒞 ⌄ T| has them as well.

  module _ {{_ : hasCoproducts 𝒞}} where
    instance
      hasCoproducts:𝒞⌄T : hasCoproducts (𝒞 ⌄ T)
      (hasCoproducts:𝒞⌄T hasCoproducts.+ a) b = ` ⟨ a ⟩ + ⟨ b ⟩ `
      ⟨ isCoproduct.ι₀ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒞⌄T) ⟩ = ι₀ ◆ return
      ⟨ isCoproduct.ι₁ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒞⌄T) ⟩ = ι₁ ◆ return
      ⟨ isCoproduct.[_,_] (hasCoproducts.isCoproduct:+ hasCoproducts:𝒞⌄T) f g ⟩ = [ ⟨ f ⟩ , ⟨ g ⟩ ]
      isCoproduct.reduce-+-₀ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒞⌄T) =
        let P : ι₀ ◆ return ◆ map [ _ , _ ] ◆ join ≣ _
            P = {!!}
        in P
      isCoproduct.reduce-+-₁ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒞⌄T) = {!!}
      isCoproduct.expand-+ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒞⌄T) = {!!}
  -- //

  module _ {{_ : hasInitial 𝒞}} where
    instance
      hasInitial:𝒞⌄T : hasInitial (𝒞 ⌄ T)
      ⟨ hasInitial.𝟘 hasInitial:𝒞⌄T ⟩ = 𝟘
      ⟨ isInitial.𝟘-elim (hasInitial.isInitial:𝟘 hasInitial:𝒞⌄T) b ⟩ = 𝟘-elim _
      isInitial.expand-𝟘 (hasInitial.isInitial:𝟘 hasInitial:𝒞⌄T) f = expand-𝟘 _


