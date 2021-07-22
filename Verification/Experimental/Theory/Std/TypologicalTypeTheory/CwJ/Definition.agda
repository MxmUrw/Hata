
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition where

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


module _ {𝑖 𝑗 : 𝔏} where
  record Notation:hasInterpret (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field ⟦_⟧ : A -> B

  open Notation:hasInterpret {{...}} public


module _ {𝑖 : 𝔏} {𝑗 : 𝔏 ^ 3} {K : 𝒰 𝑖} {𝒞 : 𝒰 _} {{_ : 𝒞 is MonoidalCategory 𝑗}} where

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

Kinding : ∀ (𝑖 : 𝔏) -> _
Kinding 𝑖 = _ :& isKinding {𝑖}

-- ⊦
-- ⫞ 	⫟
-- U+2AEx 	⫠ 	⫡ 	⫢ 	⫣ 	⫤ 	⫥ 	⫦ 	⫧ 	⫨ 	⫩ 	⫪ 	⫫ 	⫬ 	⫭ 

module _ {𝑖 : 𝔏} {A : 𝒰 𝑖} where
  toCtx : List A -> Ctx A
  toCtx [] = []
  toCtx (x ∷ a) = ([] ,, x) ⋆ toCtx a

record isCwJ {𝑗 : 𝔏} (K : Kinding 𝑗) {𝑖 : 𝔏 ^ 3} (𝒞 : MonoidalCategory 𝑖) : 𝒰 (𝑗 ､ 𝑖) where
  field ⊦ : ⟨ K ⟩ -> ⟨ 𝒞 ⟩
  -- field {{hasAction-l:K}} : hasAction-l ′(List ⟨ K ⟩)′ (⟨ 𝒞 ⟩ since isSetoid:byCategory)
  -- field {{hasDistrAction-l:K}} : hasDistributiveAction-l ′(List ⟨ K ⟩)′ ′ ⟨ 𝒞 ⟩ ′
  -- field {{isFunctor:CwJAction}} : ∀ {Γ : List ⟨ K ⟩} -> isFunctor ′ ⟨ 𝒞 ⟩ ′ ′ ⟨ 𝒞 ⟩ ′  (λ x -> Γ ↷ x)
  field varTake : ∀{Γ : List ⟨ K ⟩} {a : ⟨ K ⟩} -> (rec ⊦ Γ ⊗ ⊦ (∂ₖ a)) ⟶ (⊦ a) ⊗ rec ⊦ Γ
  -- (( Γ ⋆ ⦋ a ⦌) ↷ ⊦ a)
  field varProj : ∀{Γ : List ⟨ K ⟩} {a : ⟨ K ⟩} -> Γ ⊨-var a -> rec ⊦ Γ ⟶ (rec ⊦ Γ ⊗ ⊦ a)
  -- field varSkip : ∀{Γ : List ⟨ K ⟩} {a : ⟨ K ⟩} {x} -> (((Γ ↷ ⊦ (∂ₖ a)) ⋆ (Γ ↷ x)) ⟶ ((Γ ⋆ ⦋ a ⦌) ↷ x))
  field diag : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ a ⊗ a
  field braid  : ∀{a b : ⟨ 𝒞 ⟩} -> a ⊗ b ⟶ b ⊗ a

  -- field unit-l-⊗ : ∀{a : ⟨ 𝒞 ⟩} -> (◌ ⊗ a) ⟶ a
  -- field unit-l-⊗-⁻¹ : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ (◌ ⊗ a)

open isCwJ {{...}} public

CategoryWithJudgements : (K : Kinding 𝑗) (𝑖 : 𝔏 ^ 3) -> _
CategoryWithJudgements K (𝑖) = MonoidalCategory (𝑖 ⌄ 0 ⋯ 2) :& isCwJ K 

macro
  CwJ : (K : Kinding 𝑗) -> ∀ 𝑖 -> SomeStructure
  CwJ K 𝑖 = #structureOn (CategoryWithJudgements K 𝑖)

module _ {K : Kinding 𝑗} {𝒞 : 𝒰 _} {{_ : CwJ K 𝑖 on 𝒞}} where
  ⟦_⟧-LK : List ⟨ K ⟩ -> 𝒞
  ⟦_⟧-LK = rec ⊦

  ⟦_⟧-CJ : Jdg ⟨ K ⟩ -> 𝒞
  ⟦_⟧-CJ (Γ ⊢ α) = rec ⊦ Γ ⊗ ⊦ α

  ⟦_⟧-LCJ : List (Jdg ⟨ K ⟩) -> 𝒞
  ⟦_⟧-LCJ = rec ⟦_⟧-CJ

  -- instance
  --   Notation:hasInterpret:CwJ : Notation:hasInterpret (List ⟨ K ⟩) 𝒞
  --   Notation:hasInterpret:CwJ = record { ⟦_⟧ = ⟦_⟧-LK }

  instance
    Notation:hasInterpret:CwJ1 : Notation:hasInterpret (Jdg ⟨ K ⟩) 𝒞
    Notation:hasInterpret:CwJ1 = record { ⟦_⟧ = ⟦_⟧-CJ }

  instance
    Notation:hasInterpret:CwJ2 : Notation:hasInterpret (List (Jdg ⟨ K ⟩)) 𝒞
    Notation:hasInterpret:CwJ2 = record { ⟦_⟧ = rec ⟦_⟧ }

  JHom : List (Jdg ⟨ K ⟩) -> Jdg ⟨ K ⟩ -> 𝒰 _
  JHom 𝔍 α = ⟦ 𝔍 ⟧ ⟶ ⟦ α ⟧

  private
    instance
      _ : isSetoid 𝒞
      _ = isSetoid:byCategory

  ≀⟦⟧≀ : {Γ Γ' : List (Jdg ⟨ K ⟩)} -> Γ ∼ Γ' -> ⟦ Γ ⟧ ≅ ⟦ Γ' ⟧
  ≀⟦⟧≀ {Γ} {Γ'} refl-≣ = refl

  ⟦⊗⟧ : {Γ Δ : List (Jdg ⟨ K ⟩)} -> ⟦ Γ ⋆ Δ ⟧ ≅ ⟦ Γ ⟧ ⊗ ⟦ Δ ⟧
  ⟦⊗⟧ {⦋⦌} {D} = unit-l-⋆ ⁻¹
  ⟦⊗⟧ {x ∷ G} {D} = (refl ≀⋆≀ ⟦⊗⟧ {Γ = G}) ∙ assoc-r-⋆

  -- ⟦↷-Jdg⟧ : ∀{Γ : List ⟨ K ⟩} -> {α : (Jdg ⟨ K ⟩)} -> ⟦ Γ ↷ α ⟧-CJ ≅ Γ ↷ ⟦ α ⟧-CJ
  -- ⟦↷-Jdg⟧ = assoc-l-↷



  -- ⟦↷-ListJdg⟧ : ∀{Γ : List ⟨ K ⟩} -> {Δ : List (Jdg ⟨ K ⟩)} -> ⟦ Γ ↷ Δ ⟧-LCJ ≅ Γ ↷ ⟦ Δ ⟧-LCJ
  -- ⟦↷-ListJdg⟧ {Γ} {⦋⦌} = absorb-r-↷ ⁻¹
  -- ⟦↷-ListJdg⟧ {Γ} {x ∷ D} =
  --   ⟦ Γ ↷ x ⟧ ⊗ ⟦ Γ ↷ D ⟧       ⟨ ⟦↷-Jdg⟧ ≀⋆≀ ⟦↷-ListJdg⟧ {Γ} {D} ⟩-∼
  --   (Γ ↷ ⟦ x ⟧) ⊗ (Γ ↷ ⟦ D ⟧)   ⟨ distr-l-↷ ⁻¹ ⟩-∼
  --   Γ ↷ (⟦ x ⟧ ⊗ ⟦ D ⟧)          ∎

    -- ⟦ Γ ↷ x ⟧-CJ ⊗ ⟦ Γ ↷ D ⟧-LCJ       ⟨ ⟦↷-Jdg⟧ ≀⋆≀ ⟦↷-ListJdg⟧ {Γ} {D} ⟩-∼
    -- (Γ ↷ ⟦ x ⟧-CJ) ⊗ (Γ ↷ ⟦ D ⟧-LCJ)   ⟨ distr-l-↷ ⁻¹ ⟩-∼
    -- Γ ↷ (⟦ x ⟧-CJ ⊗ ⟦ D ⟧-LCJ)          ∎





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


module _ {K : Kinding 𝑙} where
  module _ (𝒞 : CwJ K 𝑖) (𝒟 : CwJ K 𝑗) where
    record isCwJHom (F : Functor ′ ⟨ 𝒞 ⟩ ′ ′ ⟨ 𝒟 ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where

    CwJHom = _ :& isCwJHom
{-
    -}

-- module _ {𝒞 : 𝒰 _} {K : Kinding 𝑗} {{_ : 𝒞 is CwJ K 𝑖}} where
--   ▼₁ : Rule-⦿ ⟨ K ⟩ -> 𝒰 _
--   ▼₁ = rec-𝖱-⦿ JObj
{-
-}

