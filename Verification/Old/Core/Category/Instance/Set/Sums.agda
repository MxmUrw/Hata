
module Verification.Old.Core.Category.Instance.Set.Sums where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Limit.Kan.Definition
open import Verification.Old.Core.Category.Limit.Kan.Terminal
open import Verification.Old.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Old.Core.Category.Limit.Definition
-- open import Verification.Old.Core.Category.Limit.Product
-- open import Verification.Old.Core.Category.Limit.Equalizer
-- open import Verification.Old.Core.Category.Monad
open import Verification.Old.Core.Category.Instance.SmallCategories
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Homotopy.Level

open import Verification.Old.Core.Category.Instance.Set.Definition

_+-Set_ : Set 𝑖 -> Set 𝑗 -> Set (𝑖 ､ 𝑗)
⟨ A +-Set B ⟩ = ⟨ A ⟩ +-𝒰 ⟨ B ⟩
IHType.hlevel (of (A +-Set B)) = {!!}




