
module Verification.Core.Algebra.Monoid.Free.Instance.Category where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Set.Setoid.As.Groupoid
-- open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Algebra.Monoid.Free.Definition
open import Verification.Core.Category.Std.Groupoid.Definition

module _ {A : 𝒰 𝑖} where
  instance
    isCategory:Free-𝐌𝐨𝐧 : isCategory {_ , _} (Free-𝐌𝐨𝐧 A)
    isCategory:Free-𝐌𝐨𝐧 = isCategory:bySetoid

    isGroupoid:Free-𝐌𝐨𝐧 : isGroupoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isGroupoid:Free-𝐌𝐨𝐧 = isGroupoid:bySetoid


  










