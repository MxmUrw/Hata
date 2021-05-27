
module Verification.Core.Category.Instance.Set.Sums where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Functor.Adjunction
open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Kan.Terminal
open import Verification.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Core.Category.Limit.Definition
-- open import Verification.Core.Category.Limit.Product
-- open import Verification.Core.Category.Limit.Equalizer
-- open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Category.Lift
open import Verification.Core.Homotopy.Level

open import Verification.Core.Category.Instance.Set.Definition

_+-Set_ : Set 𝑖 -> Set 𝑗 -> Set (𝑖 ､ 𝑗)
⟨ A +-Set B ⟩ = ⟨ A ⟩ +-𝒰 ⟨ B ⟩
IHType.hlevel (of (A +-Set B)) = {!!}




