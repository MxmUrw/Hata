
module Verification.Core.Category.Std.RelativeMonad.Finitary.Definition where

open import Verification.Conventions

-- open import Verification.Core.Data.Nat.Free
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category

open import Verification.Core.Category.Std.RelativeMonad.Definition

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed


module _ (I : 𝒰 𝑖) where
  private
    fin : 𝐅𝐢𝐧𝐈𝐱 I -> (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖))
    fin = 𝑓𝑢𝑙𝑙 _ 𝑒𝑙
  macro
    𝑓𝑖𝑛 = #structureOn fin

  FinitaryRelativeMonad : 𝒰 _
  FinitaryRelativeMonad = RelativeMonad 𝑓𝑖𝑛





