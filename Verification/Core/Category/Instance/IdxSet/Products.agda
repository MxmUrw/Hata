
module Verification.Core.Category.Instance.IdxSet.Products where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Functor.Adjunction
open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Kan.Terminal
open import Verification.Core.Category.Limit.Kan.Equalizer
open import Verification.Core.Category.Limit.Kan.Product
-- open import Verification.Core.Category.Limit.Definition
-- open import Verification.Core.Category.Limit.Product
-- open import Verification.Core.Category.Limit.Equalizer
-- open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Category.Lift
open import Verification.Core.Homotopy.Level

open import Verification.Core.Category.Instance.IdxSet.Definition
open import Verification.Core.Category.Instance.Set.Products


module _ {K : 𝒰 𝑘} {𝑖} where
  instance
    Terminal:IdxSet : Terminal (` IdxSet K 𝑖 `)
    ⟨ ⟨ Terminal:IdxSet ⟩ ⟩ _ = Lift 𝟙-𝒰
    of ⟨ Terminal:IdxSet ⟩ = {!!}
    of Terminal:IdxSet = {!!}

  -- instance
  --   hasProducts:IdxSet : hasProducts (` IdxSet K 𝑖 `)
  --   hasProducts:IdxSet = {!!}






