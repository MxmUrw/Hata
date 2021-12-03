
module Verification.Core.Data.Substitution.Property.Base where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Set.Setoid.Morphism.Property
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Function.Property
-- open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.SeparatingFamily

open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Indexed.Instance.SeparatingFamily
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory

open import Verification.Core.Data.Substitution.Variant.Base.Definition


-- if the indexing set is only ⊤
module §-⧜𝐒𝐮𝐛𝐬𝐭-⊤ {T : RelativeMonad (𝑓𝑖𝑛 (⊤-𝒰 {ℓ₀}))} where
  prop-1 : ∀{a b : 人ℕ} -> (f : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = T} (incl a) (incl b)) -> 人List (ix (⟨ T ⟩ (incl b)) tt)
  prop-1 {.(isMonoid.◌ isMonoid:Free-𝐌𝐨𝐧)} {b} ◌-⧜ = ◌
  prop-1 {(incl tt)} {b} (incl x) = incl x
  prop-1 {.((isMonoid:Free-𝐌𝐨𝐧 isMonoid.⋆ _) _)} {b} (f ⋆-⧜ g) = prop-1 f ⋆ prop-1 g


