
module Verification.Core.Data.Language.HindleyMilner.Helpers where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Computation.Unification.Definition





module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} (C : ∀{a} -> B a -> 𝒰 𝑘) where
  data Listᴰ² : {as : List A} (bs : Listᴰ B as) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    [] : Listᴰ² []
    _∷_ : ∀{a as} -> {b : B a} {bs : Listᴰ B as} -> (c : C b) -> (cs : Listᴰ² bs) -> Listᴰ² (b ∷ bs)



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
  size-⋆Listᴰ : ∀{m} -> ⋆Listᴰ F m -> ⋆List A
  size-⋆Listᴰ {m} _ = m

module _ {A : 𝒰 𝑖} {F : A -> 𝒰 𝑗} where
  size-Listᴰ : ∀{m} -> Listᴰ F m -> List A
  size-Listᴰ {m} _ = m

  split-Listᴰ : ∀{as : List A} {a : A} -> Listᴰ F (a ∷ as) -> (F a) × Listᴰ F as
  split-Listᴰ (b ∷ xs) = b , xs


module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where
  lookup-Listᴰ : ∀{as : List A} -> (xs : Listᴰ B as) -> ∀{a} -> (as ∍♮ a) -> B a
  lookup-Listᴰ (b ∷ xs) incl = b
  lookup-Listᴰ (b ∷ xs) (skip p) = lookup-Listᴰ xs p

module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {C : ∀{a} -> B a -> 𝒰 𝑘} where
  lookup-Listᴰ² : ∀{as : List A} -> {xs : Listᴰ B as} -> (ys : Listᴰ² C xs) -> ∀{a} -> (p : as ∍♮ a) -> C (lookup-Listᴰ xs p)
  lookup-Listᴰ² (c ∷ ys) incl = c
  lookup-Listᴰ² (c ∷ ys) (skip p) = lookup-Listᴰ² ys p

  split-Listᴰ² : ∀{as : List A} {a : A} {bs : Listᴰ B as} {b : B a} -> Listᴰ² C (b ∷ bs) -> (C b) × Listᴰ² C bs
  split-Listᴰ² (b ∷ xs) = b , xs

