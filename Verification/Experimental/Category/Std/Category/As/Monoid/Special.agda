
module Verification.Experimental.Category.Std.Category.As.Monoid.Special where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Special
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Sized.Definition
open import Verification.Experimental.Category.Std.Category.As.Monoid.Definition

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






