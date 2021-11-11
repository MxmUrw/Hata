
module Verification.Core.Category.Std.Category.As.Monoid.Special where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidWithZero.Special
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Category.As.Monoid.Definition

module _ {𝒞 : 𝒰 _} {{_ : SizedCategory 𝑖 on 𝒞}} where


  Special-PathMon : Submonoid (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 ′ 𝒞 ′)
  Special-PathMon = ′ S ′
    where
      S : 𝖯𝖺𝗍𝗁𝖬𝗈𝗇 ′ 𝒞 ′ -> Prop _
      S [] = ⊤
      S idp = ⊤
      S (arrow {a} {b} f) = ∣ Lift (sizeO b ≪ sizeO a) ∣

      instance
        isSubsetoid:S : isSubsetoid S
        isSubsetoid:S = {!!}

      instance
        isSubmonoid:S : isSubmonoid ′ S ′
        isSubmonoid:S = {!!}


  instance
    hasSpecial:PathMon : hasSpecial (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 ′ 𝒞 ′)
    hasSpecial:PathMon = record { Special = Special-PathMon }






