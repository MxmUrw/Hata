
module Verification.Experimental.Data.Renaming.Definition where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Experimental.Category.Std.Morphism.EpiMono

open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.NormalFiniteIndexed.Definition


module _ (A : 𝒰 𝑖) where
  ♮Renaming : 𝒰 _
  ♮Renaming = 𝐒𝐮𝐛ₘₒₙₒ (♮𝐅𝐢𝐧𝐈𝐱 A)

  macro
    ♮𝐑𝐞𝐧 = #structureOn ♮Renaming

  Renaming : 𝒰 _
  Renaming = 𝐒𝐮𝐛ₘₒₙₒ (𝐅𝐢𝐧𝐈𝐱 A)

  macro
    𝐑𝐞𝐧 = #structureOn Renaming





