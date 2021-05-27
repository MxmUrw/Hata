
module Verification.Core.Category.Functor.Presheaf where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Instance.Opposite public

-- ===* Presheaves

-- [Hide]
mirror-Functor : ∀{𝒞 : Category 𝑖} {𝒟 : Category 𝑗} -> Functor 𝒞 (𝒟 ᵒᵖ) -> Functor (𝒞 ᵒᵖ) 𝒟
⟨ mirror-Functor F ⟩ = ⟨ F ⟩
IFunctor.map (of mirror-Functor F) = map
IFunctor.functoriality-id (of mirror-Functor F) = functoriality-id
IFunctor.functoriality-◆ (of mirror-Functor F) = functoriality-◆
IFunctor.functoriality-≣ (of mirror-Functor F) = functoriality-≣

mirror-Nat : ∀{𝒞 : Category 𝑖} {𝒟 : Category 𝑗} -> {F G : Functor 𝒞 (𝒟 ᵒᵖ)} -> (α : Natural F G) -> Natural (mirror-Functor G) (mirror-Functor F)
⟨ mirror-Nat a ⟩ {x} = ⟨ a ⟩
INatural.naturality (of mirror-Nat a) = λ f -> sym (naturality f)
-- //


-- [Definition]
-- | A presheaf on a category |𝒞| is simply a functor |𝒞 ᵒᵖ ⟶ Set|.
PSh : (𝒞 : Category 𝑖) -> (𝑗 : 𝔏) -> 𝒰 _
PSh 𝒞 𝑗 = Functor (𝒞 ᵒᵖ) ` Set 𝑗 `
-- //

