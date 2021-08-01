
module Verification.Experimental.Algebra.Monoid.Free.Instance.Category where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Free
open import Verification.Experimental.Set.Setoid.As.Category
open import Verification.Experimental.Set.Setoid.As.Groupoid
-- open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Algebra.Monoid.Free.Definition
open import Verification.Experimental.Category.Std.Groupoid.Definition

module _ {A : 𝒰 𝑖} {𝑘 : 𝔏} where
  instance
    isCategory:Free-𝐌𝐨𝐧 : isCategory {_ , 𝑘} (Free-𝐌𝐨𝐧 A)
    isCategory:Free-𝐌𝐨𝐧 = isCategory:bySetoid

    isGroupoid:Free-𝐌𝐨𝐧 : isGroupoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isGroupoid:Free-𝐌𝐨𝐧 = isGroupoid:bySetoid


  










