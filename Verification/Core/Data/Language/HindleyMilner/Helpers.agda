
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


module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-D人List : ∀{m} -> D人List F m -> 人List A
  size-D人List {m} _ = m

module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-DList : ∀{m} -> DList F m -> List A
  size-DList {m} _ = m

  split-DList : ∀{as : List A} {a : A} -> DList F (a ∷ as) -> (F a) × DList F as
  split-DList (b ∷ xs) = b , xs


module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where
  lookup-DList : ∀{as : List A} -> (xs : DList B as) -> ∀{a} -> (as ∍♮ a) -> B a
  lookup-DList (b ∷ xs) incl = b
  lookup-DList (b ∷ xs) (skip p) = lookup-DList xs p

module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {C : ∀{a} -> B a -> 𝒰 𝑘} where
  lookup-DDList : ∀{as : List A} -> {xs : DList B as} -> (ys : DDList C xs) -> ∀{a} -> (p : as ∍♮ a) -> C (lookup-DList xs p)
  lookup-DDList (c ∷ ys) incl = c
  lookup-DDList (c ∷ ys) (skip p) = lookup-DDList ys p

  split-DDList : ∀{as : List A} {a : A} {bs : DList B as} {b : B a} -> DDList C (b ∷ bs) -> (C b) × DDList C bs
  split-DDList (b ∷ xs) = b , xs

