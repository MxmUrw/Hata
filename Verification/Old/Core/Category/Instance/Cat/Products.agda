
module Verification.Old.Core.Category.Instance.Cat.Products where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Functor
-- open import Verification.Old.Core.Category.Functor.Adjunction
-- open import Verification.Old.Core.Category.Limit.Kan.Definition
-- open import Verification.Old.Core.Category.Limit.Kan.Terminal
-- open import Verification.Old.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Old.Core.Category.Limit.Kan.Product
-- open import Verification.Old.Core.Category.Instance.Type
-- open import Verification.Old.Core.Category.Instance.Cat
-- open import Verification.Old.Core.Category.Instance.SmallCategories
-- open import Verification.Old.Core.Category.FreeCategory
-- open import Verification.Old.Core.Category.Quiver
-- open import Verification.Old.Core.Category.Instance.Set.Definition
-- open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Homotopy.Level
open import Verification.Old.Core.Order.Lattice
open import Verification.Old.Core.Order.Instance.Level
open import Verification.Old.Core.Order.Instance.Product

open import Verification.Old.Core.Category.Instance.Cat.Definition
-- open import Verification.Old.Core.Category.Instance.Set.Products


_Ã-Cat_ : Category ð -> Category ð -> Category (ð â¨ ð)
â¨ ð Ã-Cat ð â© = â¨ ð â© Ã-ð° â¨ ð â©
isCategory.Hom (of (ð Ã-Cat ð)) (aâ , aâ) (bâ , bâ) = aâ â¶ bâ Ã-ð° aâ â¶ bâ
isCategory._â£_ (of (ð Ã-Cat ð)) (fâ , fâ) (gâ , gâ) = (fâ â£ gâ) Ã-ð° (fâ â£ gâ)
isCategory.isEquivRel:â£ (of (ð Ã-Cat ð)) = {!!}
isCategory.id (of (ð Ã-Cat ð)) = (id , id)
isCategory._â_ (of (ð Ã-Cat ð)) (fâ , fâ) (gâ , gâ) = (fâ â gâ , fâ â gâ)
isCategory.unit-l-â (of (ð Ã-Cat ð)) = {!!}
isCategory.unit-r-â (of (ð Ã-Cat ð)) = {!!}
isCategory.unit-2-â (of (ð Ã-Cat ð)) = {!!}
isCategory.assoc-l-â (of (ð Ã-Cat ð)) = {!!}
isCategory.assoc-r-â (of (ð Ã-Cat ð)) = {!!}
isCategory._â_ (of (ð Ã-Cat ð)) = {!!}

