
module Verification.Core.Data.Renaming.Definition where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Core.Category.Std.Morphism.EpiMono

open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.NormalFiniteIndexed.Definition


module _ (A : 𝒰 𝑖) where
  ♮Renaming : 𝒰 _
  ♮Renaming = 𝐒𝐮𝐛ₘₒₙₒ (♮𝐅𝐢𝐧𝐈𝐱 A)

  macro
    ♮𝐑𝐞𝐧 = #structureOn ♮Renaming

  Renaming : 𝒰 _
  Renaming = 𝐒𝐮𝐛ₘₒₙₒ (𝐅𝐢𝐧𝐈𝐱 A)

  macro
    𝐑𝐞𝐧 = #structureOn Renaming





