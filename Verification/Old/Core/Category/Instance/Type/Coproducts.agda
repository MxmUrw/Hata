
module Verification.Old.Core.Category.Instance.Type.Coproducts where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type.Definition
open import Verification.Old.Core.Category.Limit.Specific
-- open import Verification.Old.Core.Category.Instance.Functor
-- open import Verification.Old.Core.Category.Functor.Adjunction
-- open import Verification.Old.Core.Category.Limit.Kan.Definition
-- open import Verification.Old.Core.Category.Limit.Kan.Terminal
-- open import Verification.Old.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Old.Core.Category.Limit.Definition
-- open import Verification.Old.Core.Category.Limit.Product
-- open import Verification.Old.Core.Category.Limit.Equalizer
-- open import Verification.Old.Core.Category.Monad
-- open import Verification.Old.Core.Category.Instance.SmallCategories
-- open import Verification.Old.Core.Category.FreeCategory
-- open import Verification.Old.Core.Category.Quiver
-- open import Verification.Old.Core.Category.Instance.Set.Definition
-- open import Verification.Old.Core.Category.Lift
-- open import Verification.Old.Core.Homotopy.Level

-- open import Verification.Old.Core.Category.Instance.Set.Definition

-- _+-𝒰_ : Set 𝑖 -> Set 𝑗 -> Set (𝑖 ､ 𝑗)
-- ⟨ A +-𝒰 B ⟩ = ⟨ A ⟩ +-𝒰 ⟨ B ⟩
-- IHType.hlevel (of (A +-Set B)) = {!!}

instance
  hasCoproducts:𝒰 : ∀{𝑖 : 𝔏} -> hasCoproducts (` 𝒰 𝑖 `)
  hasCoproducts._+_ hasCoproducts:𝒰 = _+-𝒰_
  isCoproduct.ι₀ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒰) = {!!}
  isCoproduct.ι₁ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒰) = {!!}
  isCoproduct.[_,_] (hasCoproducts.isCoproduct:+ hasCoproducts:𝒰) = {!!}
  isCoproduct.reduce-+-₀ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒰) = {!!}
  isCoproduct.reduce-+-₁ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒰) = {!!}
  isCoproduct.expand-+ (hasCoproducts.isCoproduct:+ hasCoproducts:𝒰) = {!!}

