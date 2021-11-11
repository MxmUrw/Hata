
module Verification.Core.Category.Std.Bicategory.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Natural.Instance.Category

record isBicategory {𝑗 : 𝔏 ^ 3} {𝑖 : 𝔏} (𝒞 : 𝒰 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  field Cell₁ : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)
  field {{isCategory:Cell₁}} : ∀{a b} -> isCategory {𝑗 ⌄ 1 ⋯ 2} (Cell₁ a b)

  Cell : 𝒞 -> 𝒞 -> Category 𝑗
  Cell a b = ′ Cell₁ a b ′


  field id₁ : ∀{a} -> Cell₁ a a
  field ◆⃨₁ : ∀{a b c : 𝒞} -> Functor (Cell a b ×-𝐂𝐚𝐭 Cell b c) (Cell a c)

  field unit₁-r-◆ : ∀{a b : 𝒞} -> ⧼ Const id₁ , id-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ◆⃨₁ ∼ idOn (Cell a b)
  field unit₁-l-◆ : ∀{a b : 𝒞} -> ⧼ Const id₁ , id-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ◆⃨₁ ∼ idOn (Cell a b)
  -- field assoc₁-l-◆ : ∀{a b c d : 𝒞} -> 


  -- Cell₁ : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)
  -- Cell₁ a b = ⟨ Cell a b ⟩



  -- field Cell₁ : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)
  -- field {{isCategory:Cell₁}} : ∀{a b} -> isCategory {𝑗 ⌄ 1 ⋯ 2} (Cell₁ a b)

  -- field id₁ : ∀{a} -> Cell₁ a a
  -- field ◆⃨₁ᵘ : ∀{a b c} -> (Cell₁ a b × Cell₁ b c) -> Cell₁ a c

  -- field {{isFunctor:◆⃨₁}} : ∀{a b c} -> isFunctor ′(Cell₁ a b ×-𝒰 Cell₁ b c)′ ′ Cell₁ a c ′ ◆⃨₁ᵘ

  -- field unit₁-l-◆ : ∀{a} -> 




  -- Cell₂ : ∀{a b} -> (f g : Cell₁ a b) -> 𝒰 _
  -- Cell₂ f g = f ⟶ g

  -- field Cell₂ : ∀{a b : 𝒞} -> (f g : Cell₁ a b) -> 𝒰 (𝑗 ⌄ 1)












