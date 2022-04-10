
{-# OPTIONS --experimental-lossy-unification #-}

-- NOTE
-- This file only typechecks with --experimental-lossy-unification,
-- because at some places unification of morphisms in 𝐅𝐮𝐥𝐥 would
-- need annotations otherwise.
-- With --experimental-lossy-unification, we do not need those.
--

module Verification.Core.Data.FiniteIndexed.Instance.ExternallyFinitelyAtomic where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Discrete
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
open import Verification.Core.Data.List.Variant.Binary.Element.Properties
-- open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Category.Construction.Coproduct
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Functor.Representable2
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed

-- open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated
open import Verification.Core.Category.Std.Category.Structured.Atomic.Variant.ExternallyFinitelyAtomic.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition

open import Verification.Core.Data.FiniteIndexed.Instance.ExternalFiniteAtoms




