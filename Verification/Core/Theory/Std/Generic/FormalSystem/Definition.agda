
module Verification.Core.Theory.Std.Generic.FormalSystem.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Specific.MetaTermsCalculus2.Pattern.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Substitution.Variant.Normal.Definition
open import Verification.Core.Computation.Unification.Definition



record isFormalSystem {𝑗} {𝑖} (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  field Type : A -> 𝒰 𝑗
  field Termsᵘ : (a : A) -> 𝐅𝐢𝐧𝐈𝐱 (Type a) -> 𝐈𝐱 (Type a) (𝐔𝐧𝐢𝐯 𝑗)
  field {{isFunctor:Terms}} : ∀{a} -> isFunctor (𝐅𝐢𝐧𝐈𝐱 (Type a)) (𝐈𝐱 (Type a) (𝐔𝐧𝐢𝐯 𝑗)) (Termsᵘ a)
  field {{isRelativeMonad:Terms}} : ∀{a : A} -> isRelativeMonad (𝑓𝑖𝑛 (Type a)) (′ Termsᵘ a ′)

  macro
    Terms : ∀(a : A) -> SomeStructure
    Terms a = #structureOn (Termsᵘ a)

open isFormalSystem {{...}} public

FormalSystem : ∀ (𝑗 : 𝔏 ^ 2) -> 𝒰 _
FormalSystem 𝑗 = 𝒰 (𝑗 ⌄ 0) :& isFormalSystem {𝑗 ⌄ 1}






module _ {𝒮 : 𝒰 𝑖} {{_ : isFormalSystem {𝑗} 𝒮}} (𝑨 : 𝒮) where
  𝐂𝐭𝐱ᵘ : 𝒰 _
  𝐂𝐭𝐱ᵘ = ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  macro 𝐂𝐭𝐱 = #structureOn 𝐂𝐭𝐱ᵘ

  ♮𝐂𝐭𝐱ᵘ : 𝒰 _
  ♮𝐂𝐭𝐱ᵘ = ♮𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  macro ♮𝐂𝐭𝐱 = #structureOn ♮𝐂𝐭𝐱ᵘ

-- module _ {𝒮 : FormalSystem 𝑖} {a : ⟨ 𝒮 ⟩} where
module _ {𝒮 : 𝒰 𝑖} {{_ : isFormalSystem {𝑗} 𝒮}} {𝑨 : 𝒮} where
  -- _⊢_ : ⋆List (Type 𝑨) -> Type 𝑨 -> 𝒰 _
  -- _⊢_ Γ τ = τ' ⟶ Γ'
  --   where
  --     Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  --     Γ' = incl (Γ)

  --     τ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
  --     τ' = incl (incl τ)

  _⊢_ : 𝐂𝐭𝐱 𝑨 -> Type 𝑨 -> 𝒰 _
  _⊢_ Γ τ = τ' ⟶ Γ
    where
      τ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)
      τ' = incl (incl τ)

  _at_ : ∀{Γ Δ : 𝐂𝐭𝐱 𝑨} -> {α : Type 𝑨} -> (Γ ⟶ Δ) -> ⟨ Γ ⟩ ∍ α -> Δ ⊢ α
  _at_ x t = {!!}

  simpleVar : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> (⟨ Γ ⟩ ∍ τ) -> Γ ⊢ τ
  simpleVar v = ⧜subst (incl(repure _ v))

  isSimpleVariable : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> (t : Γ ⊢ τ) -> 𝒰 _
  isSimpleVariable {Γ} {τ} t = ∑ λ (v : ⟨ Γ ⟩ ∍ τ) -> t ∼ simpleVar v


record hasFullUnification (𝒮 : FormalSystem 𝑖) : 𝒰 𝑖 where
  field {{hasUnification:this}} : ∀{𝑨 : ⟨ 𝒮 ⟩} -> hasUnification (𝐂𝐭𝐱 𝑨)




record hasSimpleVariables {𝑖} (𝒮 : FormalSystem 𝑖) (𝑨 : ⟨ 𝒮 ⟩) : 𝒰 (𝑖 ⁺) where
  -- field isVariable : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> Γ ⊢ τ -> 𝒰 (𝑖 ⌄ 1)
  field VariablePath : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ α : Type 𝑨} -> Γ ⊢ τ -> ⟨ Γ ⟩ ∍ α -> 𝒰 (𝑖 ⌄ 1)
  field Width : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> Γ ⊢ τ -> 𝒰 (𝑖 ⌄ 1)
  field VariableByWidth : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> (t : Γ ⊢ τ) -> isSimpleVariable t ↔ (Width {Γ} {τ} t ≅ ⊥)
  field WidthBySubst : ∀{Γ Δ : 𝐂𝐭𝐱 𝑨} {τ α : Type 𝑨} -> (t : Γ ⊢ τ) -> (σ : Γ ⟶ Δ)
                       -> Width (t ◆ σ) ≅ Width t ⊔ (∑ λ (x : ⟨ Γ ⟩ ∍ α) -> ∑ λ (p : VariablePath t x) -> Width (σ at x))


-- record hasVariablesᴬ {𝑖} (𝒮 : FormalSystem 𝑖) (𝑨 : ⟨ 𝒮 ⟩) : 𝒰 (𝑖 ⁺) where

--   field isVariable : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> Γ ⊢ τ -> 𝒰 (𝑖 ⌄ 1)
--   field VariablePath : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ α : Type 𝑨} -> Γ ⊢ τ -> ⟨ Γ ⟩ ∍ α -> 𝒰 (𝑖 ⌄ 1)
--   field Width : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> Γ ⊢ τ -> 𝒰 (𝑖 ⌄ 1)
--   field VariableByWidth : ∀{Γ : 𝐂𝐭𝐱 𝑨} {τ : Type 𝑨} -> (t : Γ ⊢ τ) -> isVariable {Γ} {τ} t ↔ (Width {Γ} {τ} t ≅ ⊥)
--   field WidthBySubst : ∀{Γ Δ : 𝐂𝐭𝐱 𝑨} {τ α : Type 𝑨} -> (t : Γ ⊢ τ) -> (σ : Γ ⟶ Δ)
--                        -> Width (t ◆ σ) ≅ Width t ⊔ (∑ λ (x : ⟨ Γ ⟩ ∍ α) -> ∑ λ (p : VariablePath t x) -> Width (σ at x))




