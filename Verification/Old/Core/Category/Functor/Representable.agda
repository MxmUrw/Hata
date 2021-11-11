
module Verification.Old.Core.Category.Functor.Representable where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Proper
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Presheaf
open import Verification.Old.Core.Category.Instance.Set
open import Verification.Old.Core.Category.Iso
open import Verification.Old.Core.Homotopy.Level


-- like in https://github.com/agda/agda-categories/blob/master/src/Categories/Functor/Hom.agda

-- record ISetoid (A : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ､ 𝑗 ⁺) where
--   field {{ISet:this}} : ISet A
--         _∼_ : A -> A -> 𝒰 𝑗
--         {{IEquiv:∼}} : IEquiv _∼_
-- unquoteDecl Setoid setoid

-- ===* Representable functors
-- | For this concept, we first need to define the hom-functors.

-- [Definition]
-- | Let [..] be a category which is a "proper" 1-category [..].
module _ {𝒞 : Category 𝑖} {{𝒞P : I1Category 𝒞}} where

-- | - The covariant hom-functor is given for any |a : 𝒞|:
  Functor:Hom : ∀(a : ⟨ 𝒞 ⟩) -> Functor 𝒞 ` Set (𝑖 ⌄ 1) `
  (⟨ Functor:Hom a ⟩) b = ` Hom a b `
  ⟨ IFunctor.map (of Functor:Hom a) f ⟩ g = g ◆ f
  IFunctor.functoriality-id (of Functor:Hom a) x = ≣→≡ unit-r-◆
  IFunctor.functoriality-◆ (of Functor:Hom a) x = ≣→≡ assoc-r-◆
  IFunctor.functoriality-≣ (of Functor:Hom a) p f = ≣→≡ (refl ◈ p)

-- | - The contravariant hom-functor is given for any |b : 𝒞|:
  Functor:Homᵒᵖ : ∀(b : ⟨ 𝒞 ⟩) -> Functor (𝒞 ᵒᵖ) ` Set (𝑖 ⌄ 1)`
  (⟨ Functor:Homᵒᵖ b ⟩) a = ` Hom a b `
  ⟨ IFunctor.map (of Functor:Homᵒᵖ b) g ⟩ f = g ◆ f
  IFunctor.functoriality-id (of Functor:Homᵒᵖ b) _ = ≣→≡ unit-l-◆
  IFunctor.functoriality-◆ (of Functor:Homᵒᵖ b) _ = ≣→≡ assoc-l-◆
  IFunctor.functoriality-≣ (of Functor:Homᵒᵖ b) p g = ≣→≡ (p ◈ refl)
-- //

-- [Definition]
-- | - We say that a covariant functor |F : 𝒞 ᵒᵖ ⟶ Set| is corepresented by an object |x : 𝒞|, if:
  record .Old.Core.resentation (F : PSh (𝒞 ᵒᵖ) (𝑖 ⌄ 1)) (x : ⟨ 𝒞 ⟩) : 𝒰 𝑖 where
    field corep : Functor:Hom x ≅ F

  open .Old.Core.resentation public

-- | - Likewise, we say that a contravariant functor |F : 𝒞 ⟶ Set| is represented by an object |x : 𝒞|, if:
  record IRepresentation (F : PSh 𝒞 (𝑖 ⌄ 1)) (x : ⟨ 𝒞 ⟩) : 𝒰 𝑖 where
    field rep : Functor:Homᵒᵖ x ≅ F
  open IRepresentation public
-- //

unquoteDecl Representation representation = #struct "Rep" (quote IRepresentation) "x" Representation representation
unquoteDecl.Old.Core.resentation corepresentation = #struct .Old.Core." (quote .Old.Core.resentation) "x".Old.Core.resentation corepresentation



