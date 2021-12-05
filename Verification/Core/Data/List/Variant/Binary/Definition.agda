
module Verification.Core.Data.List.Variant.Binary.Definition where


open import Verification.Core.Conventions hiding (ℕ)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Instance.Monoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Set.Contradiction


----------------------------------------------------------
-- The free encoding

-- [Definition]
-- | The type [..] is defined as a data type with the following
-- constructors:
data ⋆List (A : 𝒰 𝑖) : 𝒰 𝑖 where
  -- | - An inclusion [..].
  incl : A -> ⋆List A

  -- | - Free multiplication [..].
  _⋆-⧜_ : (a b : ⋆List A) -> ⋆List A

  -- | - Free unit [..].
  ◌-⧜ : ⋆List A
-- //

-- [Hide]

{-# DISPLAY _⋆-⧜_ a b = a ⋆ b #-}
{-# DISPLAY ◌-⧜ = ◌ #-}


macro
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 : (A : 𝒰 𝑖) -> SomeStructure
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A = #structureOn (⋆List A)

-- //

