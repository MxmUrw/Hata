
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ2 where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition




record Notation:hasInterpret (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field ⟦_⟧ : A -> B

open Notation:hasInterpret {{...}} public


module _ {K : 𝒰 𝑖} {𝒞 : 𝒰 _} {{_ : 𝒞 is MonoidalCategory 𝑗}} where

  rec-𝖱-⦿ : (Jdg-⦿ K -> 𝒞) -> Rule-⦿ K -> 𝒰 _
  rec-𝖱-⦿ f (βs ⊩ β₀) = rec-Ctx-⦿ f βs ⟶ f β₀

  iFam : (Jdg-⦿ K -> 𝒞) -> Rule-⦿ K -> 𝒰 _
  iFam f β = ∀(Δ : Ctx-⦿ K) -> rec-𝖱-⦿ f (Δ ↷ β)

  -- record iFam (f : Jdg-⦿ K -> 𝒞) (β : Rule-⦿ K) : 𝒰 (𝑖 ､ (𝑗 ⌄ 1)) where
  --   constructor incl
  --   field ⟨_⟩ : ∀(Δ : Ctx-⦿ K) -> rec-𝖱-⦿ f (Δ ↷ β)




-----------------------------------
-- ==* judgement categories

record isKinding (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field ∂ₖ : A -> A

open isKinding {{...}} public

Kinding : ∀ 𝑖 -> _
Kinding 𝑖 = _ :& isKinding {𝑖}

-- ⊦
-- ⫞ 	⫟
-- U+2AEx 	⫠ 	⫡ 	⫢ 	⫣ 	⫤ 	⫥ 	⫦ 	⫧ 	⫨ 	⫩ 	⫪ 	⫫ 	⫬ 	⫭ 

module _ {A : 𝒰 𝑖} where
  toCtx : List A -> Ctx A
  toCtx [] = []
  toCtx (x ∷ a) = ([] ,, x) ⋆ toCtx a

record isCwJ (K : Kinding 𝑗) {𝑖} (𝒞 : MonoidalCategory 𝑖) : 𝒰 (𝑗 ､ 𝑖) where
  field ⊦ : ⟨ K ⟩ -> ⟨ 𝒞 ⟩
  field {{hasAction-l:K}} : hasAction-l ′(List ⟨ K ⟩)′ (⟨ 𝒞 ⟩ since isSetoid:byCategory)
  field varTake : ∀{Γ : List ⟨ K ⟩} {a : ⟨ K ⟩} -> (Γ ↷ ⊦ (∂ₖ a)) ⟶ ((Γ ⋆ ⦋ a ⦌) ↷ ⊦ a)
  field varSkip : ∀{Γ : List ⟨ K ⟩} {a : ⟨ K ⟩} {x} -> (((Γ ↷ ⊦ (∂ₖ a)) ⊗ (Γ ↷ x)) ⟶ ((Γ ⋆ ⦋ a ⦌) ↷ x))
  field diag : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ (a ⊗ a)
  field unit-l-⊗ : ∀{a : ⟨ 𝒞 ⟩} -> (◌ ⊗ a) ⟶ a
  field unit-l-⊗-⁻¹ : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ (◌ ⊗ a)

  ⟦_⟧-CJ : Jdg ⟨ K ⟩ -> ⟨ 𝒞 ⟩
  ⟦_⟧-CJ (Γ ⊢ α) = Γ ↷ ⊦ α

  instance
    Notation:hasInterpret:CwJ : Notation:hasInterpret (Jdg ⟨ K ⟩) ⟨ 𝒞 ⟩
    Notation:hasInterpret:CwJ = record { ⟦_⟧ = ⟦_⟧-CJ }

  instance
    Notation:hasInterpret:CwJ2 : Notation:hasInterpret (List (Jdg ⟨ K ⟩)) ⟨ 𝒞 ⟩
    Notation:hasInterpret:CwJ2 = record { ⟦_⟧ = rec ⟦_⟧ }

  JHom : List (Jdg ⟨ K ⟩) -> Jdg ⟨ K ⟩ -> 𝒰 _
  JHom 𝔍 α = ⟦ 𝔍 ⟧ ⟶ ⟦ α ⟧


  -- field JKind : 𝒰 𝑗
  -- field JObj : Jdg-⦿ JKind -> ⟨ 𝒞 ⟩
  -- field JHom : (β : JBoundaryT JKind) -> iFam JObj β

open isCwJ {{...}} public

CategoryWithJudgements : (K : Kinding 𝑗) (𝑖 : 𝔏 ^ 3) -> _
CategoryWithJudgements K (𝑖) = MonoidalCategory (𝑖 ⌄ 0 ⋯ 2) :& isCwJ K 

module _ {K : Kinding 𝑗} where
  instance
    isCategory:CategoryWithJudgements : ∀{𝑖} -> isCategory (CategoryWithJudgements K 𝑖)
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
  CwJ : (K : Kinding 𝑗) -> ∀ 𝑖 -> SomeStructure
  CwJ K 𝑖 = #structureOn (CategoryWithJudgements K 𝑖)


module _ {K : Kinding 𝑙} where
  module _ (𝒞 : CwJ K 𝑖) (𝒟 : CwJ K 𝑗) where
    record isCwJHom (F : Functor ′ ⟨ 𝒞 ⟩ ′ ′ ⟨ 𝒟 ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where

    CwJHom = _ :& isCwJHom

-- module _ {𝒞 : 𝒰 _} {K : Kinding 𝑗} {{_ : 𝒞 is CwJ K 𝑖}} where
--   ▼₁ : Rule-⦿ ⟨ K ⟩ -> 𝒰 _
--   ▼₁ = rec-𝖱-⦿ JObj
{-
-}
