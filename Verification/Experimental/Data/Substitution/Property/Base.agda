
module Verification.Experimental.Data.Substitution.Property.Base where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Function.Injective
open import Verification.Experimental.Set.Setoid.Morphism
open import Verification.Experimental.Set.Setoid.Morphism.Property
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Function.Property
-- open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Functor.Faithful
open import Verification.Experimental.Category.Std.Functor.Full
open import Verification.Experimental.Category.Std.Functor.EssentiallySurjective
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.SeparatingFamily

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Instance.SeparatingFamily
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Reflection.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory

open import Verification.Experimental.Data.Substitution.Definition


-- if the indexing set is only ⊤
module §-⧜𝐒𝐮𝐛𝐬𝐭-⊤ {T : RelativeMonad (𝑓𝑖𝑛 (⊤-𝒰 {ℓ₀}))} where
  prop-1 : ∀{a b : 人ℕ} -> (f : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = T} (incl a) (incl b)) -> 人List (ix (⟨ T ⟩ (incl b)) tt)
  prop-1 {.(isMonoid.◌ isMonoid:Free-𝐌𝐨𝐧)} {b} ◌-⧜ = ◌
  prop-1 {(incl tt)} {b} (incl x) = incl x
  prop-1 {.((isMonoid:Free-𝐌𝐨𝐧 isMonoid.⋆ _) _)} {b} (f ⋆-⧜ g) = prop-1 f ⋆ prop-1 g


