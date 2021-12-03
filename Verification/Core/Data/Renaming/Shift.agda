
module Verification.Core.Data.Renaming.Shift where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Core.Category.Std.Morphism.EpiMono

open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.NormalFiniteIndexed.Definition

open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal


module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where

  shiftₗ-♮𝐑𝐞𝐧 : (x : List A) -> ♮𝐑𝐞𝐧 A -> ♮𝐑𝐞𝐧 A
  shiftₗ-♮𝐑𝐞𝐧 x a = incl (incl x) ⋆ a

  module _ (x : List A) where
    macro
      𝑠ℎ𝑖𝑓𝑡ₗ-♮𝐑𝐞𝐧 = #structureOn (shiftₗ-♮𝐑𝐞𝐧 x)

  map-shiftₗ-♮𝐑𝐞𝐧 : (x : List A) {a b : ♮𝐑𝐞𝐧 A} -> a ⟶ b -> shiftₗ-♮𝐑𝐞𝐧 x a ⟶ shiftₗ-♮𝐑𝐞𝐧 x b
  map-shiftₗ-♮𝐑𝐞𝐧 x f = map-⋆-♮𝐑𝐞𝐧 (id , f)

  instance
    isFunctor:𝑠ℎ𝑖𝑓𝑡ₗ-♮𝐑𝐞𝐧 : ∀{x} -> isFunctor (♮𝐑𝐞𝐧 A) (♮𝐑𝐞𝐧 A) (𝑠ℎ𝑖𝑓𝑡ₗ-♮𝐑𝐞𝐧 x)
    isFunctor:𝑠ℎ𝑖𝑓𝑡ₗ-♮𝐑𝐞𝐧 = {!!}




