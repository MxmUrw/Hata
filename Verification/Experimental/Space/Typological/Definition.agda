
module Verification.Experimental.Space.Typological.Definition where

open import Verification.Conventions hiding (Discrete ; ∅ ; Bool ; _and_)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice


-- Definition of topological space on base from
-- https://www.sciencedirect.com/science/article/pii/S0168007205000643
--

module _ {A B : 𝒰 𝑖} where
  ↓-syntax : (ℬ : A -> B -> Prop 𝑖) -> A -> A -> A -> Prop 𝑖
  ↓-syntax ℬ a b c = ∣ ℬ c ≤ (ℬ a ∧ ℬ b) ∣

  syntax ↓-syntax ℬ a b = a ↓[ ℬ ] b

record isTypologicalBase {A : 𝒰 𝑖} {Base : 𝒰 𝑖} (ℬ : Base -> (A -> Prop 𝑖)) : 𝒰 (𝑖 ⁺) where
  -- field Base : 𝒰 𝑖
  -- field ℬ : Base -> (A -> Prop 𝑖)

record isTypological (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  constructor topological
  field Base : 𝒰 𝑖
  field ℬ : Base -> (A -> Prop 𝑖)

  _⊩_ : A -> Base -> Prop 𝑖
  _⊩_ a b = ℬ b a

  all : A -> Prop 𝑖
  all a = ∣ (∑ λ (b : Base) -> ⟨ a ⊩ b ⟩) ∣

  field covers-⊤ : all ∼ ⊤

  _↓_ : Base -> Base -> Base -> Prop 𝑖
  _↓_ a b c = ∣ ℬ c ≤ (ℬ a ∧ ℬ b) ∣

  field covers-∧ : ∀{a b : Base} -> ℬ a ∧ ℬ b ∼ ⋁ (λ (x : ⦋ a ↓[ ℬ ] b ⦌) -> ℬ ⟨ x ⟩)

  isOpen : (A -> Prop 𝑖) -> 𝒰 (𝑖 ⁺)
  isOpen U = ∑ λ (I : 𝒰 𝑖) -> ∑ λ (F : I -> Base) -> U ∼ ⋁ (ℬ ∘ F)


open isTypological {{...}} public

Typological : ∀ 𝑖 -> 𝒰 _
Typological 𝑖 = 𝒰 𝑖 :& isTypological

𝐓𝐲𝐩 : ∀ 𝑖 -> SomeStructure
𝐓𝐲𝐩 𝑖 = #structureOn (Typological 𝑖)






