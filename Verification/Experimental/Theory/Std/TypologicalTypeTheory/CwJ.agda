
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition


module _ {K : 𝒰 𝑖} {𝒞 : 𝒰 _} {{_ : 𝒞 is MonoidalCategory 𝑗}} where

  rec-𝖱-⦿ : (Jdg-⦿ K -> 𝒞) -> Rule-⦿ K -> 𝒰 _
  rec-𝖱-⦿ f (βs ⊩ β₀) = rec-Ctx-⦿ f βs ⟶ f β₀

  iFam : (Jdg-⦿ K -> 𝒞) -> Rule-⦿ K -> 𝒰 _
  iFam f β = ∀(Δ : Ctx-⦿ K) -> rec-𝖱-⦿ f (Δ ↷ β)



-----------------------------------
-- ==* judgement categories


record hasJudgements {𝑗} {𝑖} (𝒞 : MonoidalCategory 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
  field JKind : 𝒰 𝑗
  field JObj : Jdg-⦿ JKind -> ⟨ 𝒞 ⟩
  -- field JHom : (β : JBoundaryT JKind) -> iFam JObj β

open hasJudgements {{...}} public

CategoryWithJudgements : ∀ (𝑖 : 𝔏 ^ 4) -> _
CategoryWithJudgements 𝑖 = MonoidalCategory (𝑖 ⌄ 0 ⋯ 2) :& hasJudgements {𝑖 ⌄ 3}

instance
  isCategory:CategoryWithJudgements : ∀{𝑖} -> isCategory (CategoryWithJudgements 𝑖)
  isCategory.Hom isCategory:CategoryWithJudgements = (λ 𝒞 𝒟 -> Functor ′ ⟨ 𝒞 ⟩ ′ ′ ⟨ 𝒟 ⟩ ′)
  isCategory.isSetoid:Hom isCategory:CategoryWithJudgements = isSetoid:byCategory
  isCategory.id isCategory:CategoryWithJudgements = {!!}
  isCategory._◆_ isCategory:CategoryWithJudgements = {!!}
  isCategory.unit-l-◆ isCategory:CategoryWithJudgements = {!!}
  isCategory.unit-r-◆ isCategory:CategoryWithJudgements = {!!}
  isCategory.unit-2-◆ isCategory:CategoryWithJudgements = {!!}
  isCategory.assoc-l-◆ isCategory:CategoryWithJudgements = {!!}
  isCategory.assoc-r-◆ isCategory:CategoryWithJudgements = {!!}
  isCategory._◈_ isCategory:CategoryWithJudgements = {!!}

macro
  CwJ : ∀ 𝑖 -> SomeStructure
  CwJ 𝑖 = #structureOn (CategoryWithJudgements 𝑖)


module _ (𝒞 : CwJ 𝑖) (𝒟 : CwJ 𝑗) where
  record isCwJHom (F : Functor ′ ⟨ 𝒞 ⟩ ′ ′ ⟨ 𝒟 ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where

  CwJHom = _ :& isCwJHom

module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is CwJ 𝑖}} where
  ▼₁ : Rule-⦿ JKind -> 𝒰 _
  ▼₁ = rec-𝖱-⦿ JObj


