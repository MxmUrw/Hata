
module Verification.Experimental.Data.Renaming.Instance.hasEqualizers where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Function.Injective
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Property.EpiMono

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Property.Mono
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.NormalFiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full public
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid

open import Verification.Experimental.Data.Renaming.Definition

open import Verification.Experimental.Category.Std.Limit.Specific.Equalizer.Definition

module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where


  instance
    hasEqualizers:♮𝐑𝐞𝐧 : hasEqualizers (♮𝐑𝐞𝐧 A)
    hasEqualizers:♮𝐑𝐞𝐧 = {!!}




