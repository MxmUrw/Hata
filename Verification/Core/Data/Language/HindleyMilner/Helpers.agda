
module Verification.Core.Data.Language.HindleyMilner.Helpers where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries




module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} (C : ∀{a} -> B a -> 𝒰 𝑘) where
  data DDList : {as : List A} (bs : DList B as) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    [] : DDList []
    _∷_ : ∀{a as} -> {b : B a} {bs : DList B as} -> (c : C b) -> (cs : DDList bs) -> DDList (b ∷ bs)


module §-HM-Helpers where
  module _ {𝒞ᵘ : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞ᵘ}} {{_ : hasFiniteCoproducts ′ 𝒞ᵘ ′ }} where

    private macro 𝒞 = #structureOn 𝒞ᵘ
    private instance _ = isSetoidHom:⦗⦘

    prop-1 : ∀{a b : 𝒞} -> ∀{f : a ⟶ b} -> ⦗ id , elim-⊥ ⦘ ◆ f ∼ (f ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘
    prop-1 {f = f} =
      ⦗ id , elim-⊥ ⦘ ◆ f     ⟨ append-⦗⦘ ⟩-∼
      ⦗ id ◆ f , elim-⊥ ◆ f ⦘  ⟨ cong-∼ (unit-l-◆ , expand-⊥) ⟩-∼
      ⦗ f , elim-⊥ ⦘           ⟨ cong-∼ ((unit-r-◆ ⁻¹) , (unit-l-◆ ⁻¹)) ⟩-∼
      ⦗ f ◆ id , id ◆ elim-⊥ ⦘ ⟨ append-⇃⊔⇂ ⁻¹ ⟩-∼
      (f ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘  ∎



