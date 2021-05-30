
module Verification.Experimental.Data.Prop.Instance.Preorder where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Data.Prop.Instance.Setoid
open import Verification.Experimental.Data.Universe.Definition

instance
  isPreorder:Prop : isPreorder _ ′ Prop 𝑖 ′
  isPreorder._≤'_      isPreorder:Prop A B = ⟨ A ⟩ -> ⟨ B ⟩
  isPreorder.reflexive isPreorder:Prop = incl id-𝒰
  isPreorder._⟡_       isPreorder:Prop f g = incl $ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩
  isPreorder.transp-≤  isPreorder:Prop (incl (_ , p)) (incl (v , _)) f = incl (p ◆-𝒰 ⟨ f ⟩ ◆-𝒰 v)


instance
  isPartialorder:Prop : isPartialorder ′ Prop 𝑖 ′
  isPartialorder.antisym isPartialorder:Prop (incl p) (incl q) = incl (p , q)
