
{-# OPTIONS --experimental-lossy-unification #-}

-- NOTE
-- This file only typechecks with --experimental-lossy-unification,
-- because at some places unification of morphisms in 𝐅𝐮𝐥𝐥 would
-- need annotations otherwise.
-- With --experimental-lossy-unification, we do not need those.
--

module Verification.Core.Data.FiniteIndexed.Instance.Impossible.Atomic where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
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
-- open import Verification.Core.Data.Indexed.Duplicate
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

open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated
open import Verification.Core.Category.Std.Category.Structured.Atomic.Definition
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
-- open import Verification.Core.Category.Std.Limit.Representation.Colimit.Definition




--
-- Description
--
-- In this file we try to show that 𝐅𝐢𝐧𝐈𝐱 is atomic (as defined in #12),
-- but it appears to be impossible, seemingly requiring something Axiom-of-Choice-like,
-- in the definition of `ξ` below.
--



module _ {I : 𝒰 𝑖} where
  𝑠𝑖𝑛𝑔𝑙 : I -> 𝐅𝐢𝐧𝐈𝐱 I
  𝑠𝑖𝑛𝑔𝑙 i = incl (incl i)

  module _ {𝑗 : 𝔏 ^ 3} {a : I} where
    isAtom:𝑠𝑖𝑛𝑔𝑙 : isAtom 𝑗 (𝑠𝑖𝑛𝑔𝑙 a)
    isAtom:𝑠𝑖𝑛𝑔𝑙 {𝒥} D {x} xP = Proof
      where
        α : Natural D (Const x)
        α = colimitCocone xP

        βᵘ : ∀(j : ⟨ 𝒥 ⟩) -> (𝑠𝑖𝑛𝑔𝑙 a ⟶ ⟨ D ⟩ j) -> 𝑠𝑖𝑛𝑔𝑙 a ⟶ x
        βᵘ j f = f ◆ ⟨ α ⟩ j
        instance
          isSetoidHom:β : ∀{j} -> isSetoidHom (𝑠𝑖𝑛𝑔𝑙 a ⟶ ⟨ D ⟩ j) (𝑠𝑖𝑛𝑔𝑙 a ⟶ x) (βᵘ j)
          isSetoidHom:β = record { cong-∼ = λ p → p ◈ refl }

        lem-1 : ∀{j k : ⟨ 𝒥 ⟩} -> ∀(ϕ : j ⟶ k) -> ∀(f : (𝑠𝑖𝑛𝑔𝑙 a) ⟶ ⟨ D ⟩ j) -> βᵘ j f ∼  βᵘ k (⟨ mapOf (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a)) ϕ ⟩ f)
        lem-1 {j} {k} ϕ f = βᵘ j f

                ⟨ refl ⟩-∼

                f ◆ ⟨ α ⟩ j

                ⟨ refl ◈ unit-r-◆ ⁻¹ ⟩-∼

                f ◆ (⟨ α ⟩ j ◆ id)

                ⟨ refl ◈ naturality {{of α}} (ϕ) ⟩-∼

                f ◆ (mapOf D ϕ ◆ ⟨ α ⟩ k)

                ⟨ assoc-r-◆ ⟩-∼

                (f ◆ mapOf D ϕ) ◆ ⟨ α ⟩ k

                ∎

        isNatural:β : isNatural (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a)) (Const (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)) (λ j -> ′ βᵘ j ′)
        isNatural:β = natural λ ϕ → pointwise λ f -> lem-1 ϕ f

        β : Natural (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a)) (Const (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x))
        β = (λ j -> ′ βᵘ j ′) since isNatural:β

        module _ (γ : 𝐂𝐨𝐜𝐨𝐧𝐞 (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a))) where

          ξ : SetoidHom (𝑠𝑖𝑛𝑔𝑙 a ⟶ x) (pt γ)
          ξ = {!!} since {!!}

          -- (y : 𝐅𝐢𝐧𝐈𝐱 I) (γ : Natural (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a)) (Const (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ y))) where
          -- ξᵘ : SetoidHom (𝑠𝑖𝑛𝑔𝑙 a ⟶ x) (𝑠𝑖𝑛𝑔𝑙 )
          lem-2 : cocone (𝑠𝑖𝑛𝑔𝑙 a ⟶ x) β ⟶ γ
          lem-2 = record
            { pt = ξ
            ; ◺ = {!!}
            }

        Proof = record
          { colimitCocone = β
          ; colimitUniversal = record
            { elim-⊥ = lem-2 _
            ; expand-⊥ = {!!}
            }
          }

