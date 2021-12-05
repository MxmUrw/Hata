
module Verification.Core.Data.List.Variant.Binary.Instance.Category where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Set.Setoid.As.Groupoid
-- open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Category.Std.Groupoid.Definition

module _ {A : 𝒰 𝑖} where
  instance
    isCategory:⋆List : isCategory {_ , _} (⋆List A)
    isCategory:⋆List = isCategory:bySetoid

    isGroupoid:⋆List : isGroupoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isGroupoid:⋆List = isGroupoid:bySetoid


  










