
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Specific.LayeredType where

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
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition


record Layered (K : Kinding 𝑖) (𝒞 : Category 𝑗) : 𝒰 (𝑖 ⊔ (𝑗 ⌄ 0)) where
  field layer : List ⟨ K ⟩ -> ⟨ 𝒞 ⟩

open Layered public

module _ {K : Kinding 𝑖} {𝒞 : Category 𝑗} where
  instance
    Index-Notation:Layered : Index-Notation (Layered K 𝒞) (const (List ⟨ K ⟩)) (const (⊤-𝒰 {ℓ₀})) (const ⟨ 𝒞 ⟩)
    Index-Notation._⌄_ Index-Notation:Layered = λ A Γ -> layer A Γ

module _ {K : Kinding 𝑖} {𝒞 : Category 𝑗} where
  record LayeredHom (A B : Layered K 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field layer : (Γ : List ⟨ K ⟩) -> A ⌄ Γ ⟶ B ⌄ Γ


  open LayeredHom public




