
module Verification.Core.Data.Prop.Instance.Preorder where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Prop.Instance.Setoid
open import Verification.Core.Data.Universe.Definition

instance
  isPreorder:Prop : isPreorder _ ′ Prop 𝑖 ′
  isPreorder._≤_      isPreorder:Prop = ≤-Base (λ A B -> ⟨ A ⟩ -> ⟨ B ⟩)
  isPreorder.reflexive isPreorder:Prop = incl id-𝒰
  isPreorder._⟡_       isPreorder:Prop f g = incl $ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩
  isPreorder.transp-≤  isPreorder:Prop ((_ , p)) ((v , _)) f = incl (p ◆-𝒰 ⟨ f ⟩ ◆-𝒰 v)


instance
  isPartialorder:Prop : isPartialorder ′ Prop 𝑖 ′
  isPartialorder.antisym isPartialorder:Prop (incl p) (incl q) = (p , q)

-- instance
--   isPreorder:Prop : isPreorder _ ′ Prop 𝑖 ′
--   isPreorder._≤'_      isPreorder:Prop A B = ⟨ A ⟩ -> ⟨ B ⟩
--   isPreorder.reflexive isPreorder:Prop = incl id-𝒰
--   isPreorder._⟡_       isPreorder:Prop f g = incl $ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩
--   isPreorder.transp-≤  isPreorder:Prop ((_ , p)) ((v , _)) f = incl (p ◆-𝒰 ⟨ f ⟩ ◆-𝒰 v)


-- instance
--   isPartialorder:Prop : isPartialorder ′ Prop 𝑖 ′
--   isPartialorder.antisym isPartialorder:Prop (incl p) (incl q) = (p , q)
