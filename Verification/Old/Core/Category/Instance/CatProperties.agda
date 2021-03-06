
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.VHM3.Old.Core.Category.Instance.CatProperties where

open import Verification.VHM3.Old.Core.Base
open import Verification.VHM3.Old.Core.Meta
open import Verification.VHM3.Old.Core.Category.Base
open import Verification.VHM3.Old.Core.Category.Limit
open import Verification.VHM3.Old.Core.Category.Monad
open import Verification.VHM3.Old.Core.Category.Instance.Type
open import Verification.VHM3.Old.Core.Category.Instance.Cat

_ร-Category_ : Category ๐๐๐ -> Category ๐๐๐ -> Category (zipL ๐๐๐ ๐๐๐)
โจ X ร-Category Y โฉ = โจ X โฉ ร-๐ฐ โจ Y โฉ
ICategory.Hom (of (X ร-Category Y)) (a1 , a2) (b1 , b2) = Hom a1 b1 ร-๐ฐ Hom a2 b2
ICategory._โฃ_ (of (X ร-Category Y)) (f1 , g1) (f2 , g2) = (f1 โฃ f2) ร-๐ฐ (g1 โฃ g2)
ICategory.IEquiv:โฃ (of (X ร-Category Y)) = {!!}
ICategory.id (of (X ร-Category Y)) = id , id
ICategory._โ_ (of (X ร-Category Y)) (f1 , g1) (f2 , g2) = (f1 โ f2) , (g1 โ g2)
ICategory._โ_ (of (X ร-Category Y)) = {!!}
ICategory./idโ (of (X ร-Category Y)) = {!!}
ICategory./โid (of (X ร-Category Y)) = {!!}
ICategory./idโ (of (X ร-Category Y)) = {!!}
ICategory./โโโ (of (X ร-Category Y)) = {!!}
ICategory./โโแตฃ (of (X ร-Category Y)) = {!!}

hasProducts:Category : hasProducts (Category ๐๐๐)
โจ โจ has_ShapedLimits.lim hasProducts:Category D โฉ โฉ = โจ D โฉ โ ร-Category โจ D โฉ โ
of โจ has_ShapedLimits.lim hasProducts:Category D โฉ = {!!}
of (has_ShapedLimits.lim hasProducts:Category D) = {!!}


