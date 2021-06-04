
module Verification.Experimental.Theory.Type.Simple.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Computation.Question.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Theory.Computation.Question.Construction.Product
-- open import Verification.Experimental.Theory.Computation.Question.Construction.Product
-- open import Verification.Experimental.Theory.Computation.Question.Construction.MonoidalProduct


record Theory (𝑖 : 𝔏 ^ 2) : 𝒰 (𝑖 ⁺) where
  constructor theory
  field Theorem : 𝒰 (𝑖 ⌄ 0)
  field Proof : Theorem -> 𝒰 (𝑖 ⌄ 1)


record TypeTheory (𝑖 : 𝔏 ^ 5) : 𝒰 (𝑖 ⁺) where
  constructor typeTheory
  field Term : 𝒰 (𝑖 ⌄ 0)
  field Type : Category (𝑖 ⌄ 1 , 𝑖 ⌄ 2 , 𝑖 ⌄ 3)
  field _⊢_ : ⟨ Type ⟩ -> Term -> 𝒰 (𝑖 ⌄ 4)


open import Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Abstract.Checking
open import Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Definition as Λᶜ using ()
open import Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Definition using (_∣_⊢_ ; _∣_⊢_/_)


instance
  isCategory:Info : isCategory (ℓ₀ , ℓ₀) Info-Λᶜ
  isCategory:Info = {!!}

Λᶜʰ : TypeTheory _
Λᶜʰ = typeTheory Λᶜ.Term ′ Info-Λᶜ ′ _⊢ᶜ_


cath : Category 𝑖 -> Theory _
cath 𝒞 = theory (𝒞 × 𝒞) λ (x , y) → x ⟶ y

