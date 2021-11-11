
module Verification.Old.Core.Category.Instance.IdxSet.Coproducts where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Limit.Specific
-- open import Verification.Old.Core.Category.Limit.Kan.Definition
open import Verification.Old.Core.Category.Limit.Kan.Terminal
-- open import Verification.Old.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Old.Core.Category.Limit.Kan.Product
-- open import Verification.Old.Core.Category.Limit.Definition
-- open import Verification.Old.Core.Category.Limit.Product
-- open import Verification.Old.Core.Category.Limit.Equalizer
-- open import Verification.Old.Core.Category.Monad
open import Verification.Old.Core.Category.Instance.SmallCategories
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Homotopy.Level

open import Verification.Old.Core.Category.Instance.IdxSet.Definition

module _ {K : 𝒰 𝑘} where
  _+-IdxSet_ : IdxSet K 𝑖 -> IdxSet K 𝑖 -> IdxSet K (𝑖)
  ⟨ A +-IdxSet B ⟩ k = ⟨ A ⟩ k +-𝒰 ⟨ B ⟩ k
  IIdxSet.ISet:this (of (A +-IdxSet B)) = {!!}




--------------------------------------------------------------------
-- IdxSet has coproducts

  -- private
  --   P : Functor `(`𝟚` ⟶ (` IdxSet K 𝑖 `))` (` 𝟙 ⟶ (` IdxSet K 𝑖 `)`)
  --   ⟨ P ⟩ D = Diagram-𝟙 (⟨ D ⟩ (↥ ₀) +-IdxSet ⟨ D ⟩ (↥ ₁))
  --   IFunctor.map (of P) = {!!}
  --   IFunctor.functoriality-id (of P) = {!!}
  --   IFunctor.functoriality-◆ (of P) = {!!}
  --   IFunctor.functoriality-≣ (of P) = {!!}
  -- [_,_]-IdxSet : ∀{A B C : IdxSet K 𝑖} -> (f : A ⟶ C) -> (g : B ⟶ C) -> (A +-IdxSet B) ⟶ C
  -- ⟨ [ f , g ]-IdxSet ⟩ (left x) = ⟨ f ⟩ x
  -- ⟨ [ f , g ]-IdxSet ⟩ (just x) = ⟨ g ⟩ x

  [,]-IdxSet : ∀(A B C : IdxSet K 𝑖) -> (f : A ⟶ C) -> (g : B ⟶ C) -> (A +-IdxSet B) ⟶ C
  ⟨ [,]-IdxSet A B C f g ⟩ (left x) = ⟨ f ⟩ x
  ⟨ [,]-IdxSet A B C f g ⟩ (just x) = ⟨ g ⟩ x
  -- ⟨ [ f , g ]-IdxSet ⟩ (left x) = ⟨ f ⟩ x
  -- ⟨ [ f , g ]-IdxSet ⟩ (just x) = ⟨ g ⟩ x

  instance
    hasCoproducts:IdxSet : hasCoproducts (` IdxSet K 𝑖 `)
    hasCoproducts._+_ hasCoproducts:IdxSet = _+-IdxSet_
    ⟨ isCoproduct.ι₀ (hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet) ⟩ = left
    ⟨ isCoproduct.ι₁ (hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet) ⟩ = right
    isCoproduct.[ hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet , f ] g = [,]-IdxSet _ _ _ f g
    -- ⟨ isCoproduct.[ hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet , f ] g ⟩ (just x) = ⟨ g ⟩ x
    isCoproduct.reduce-+-₀ (hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet) = {!!}
    isCoproduct.reduce-+-₁ (hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet) = {!!}
    isCoproduct.expand-+ (hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet) = {!!}
    -- ⟨ hasCoproducts:IdxSet ⟩ = P
    -- IAdjoint.embed (of hasCoproducts:IdxSet) = {!!}
    -- IAdjoint.eval (of hasCoproducts:IdxSet) = {!!}
    -- IAdjoint.reduce-Adj-β (of hasCoproducts:IdxSet) = {!!}
    -- IAdjoint.reduce-Adj-η (of hasCoproducts:IdxSet) = {!!}

