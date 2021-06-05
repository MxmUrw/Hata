
module Verification.Experimental.Computation.Question.Construction.Product where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Computation.Question.Definition




macro
  _×_ : (𝒰 𝑖) [ 𝑙 ]→ (𝒰 𝑗) [ 𝑘 ]→ SomeStructure
  _×_ = λstr A ↦ λstr B ↦ #structureOn (A ×-𝒰 B)
  infixr 50 _×_

  -- (λ X -> λstr (λ B -> {!!}))
  -- (λ[] B , #structureOn (X ×-𝒰 B))

  -- _×'_ : WithStructureOnω (𝒰 𝑖) (WithStructureOn (𝒰 𝑗) SomeStructure)
  -- _×'_ = λstrω (λ X -> λstr ?)
  -- λstr (λ X -> λstr (λ B -> #structureOn (X ×-𝒰 B)))

  -- u {{UU}} {{refl-StrId}} B = #structureOn (destructEl UU u ×-𝒰 B)
  -- _×'_ u {{UU}} {{refl-StrId}} B = #structureOn (destructEl UU u ×-𝒰 B)
  -- #structureOn (A ×-𝒰 B)

-- macro
--   _×_ : ∀(A : 𝒰 𝑖) (B : 𝒰 𝑗) -> SomeStructure
--   _×_ A B = #structureOn (A ×-𝒰 B)

macro
  _+_ : ∀(A : 𝒰 𝑖) (B : 𝒰 𝑗) -> SomeStructure
  _+_ A B = #structureOn (A +-𝒰 B)


module _ {𝔓 : 𝒰 _} {𝔔 : 𝒰 _} {{_ : Question 𝑖 on 𝔓}} {{_ : Question 𝑗 on 𝔔}} where
  instance
    isQuestion:× : isQuestion _ (𝔓 × 𝔔)
    isQuestion:× = answerWith (λ (p , q) → p ‽ + q ‽)


module _ {𝔓 𝔔 : Question 𝑖} where
  private
    π₀ : (𝔓 × 𝔔) ⟶ 𝔓
    π₀ = incl (fst since reductive left)

    π₁ : (𝔓 × 𝔔) ⟶ 𝔔
    π₁ = incl (snd since reductive right)

    ⟨_,_⟩ : ∀{ℜ : Question 𝑖} -> (f : ℜ ⟶ 𝔓) -> (g : ℜ ⟶ 𝔔) -> ℜ ⟶ 𝔓 × 𝔔
    ⟨_,_⟩ f g = incl ((λ x → (⟨ ⟨ f ⟩ ⟩ x , ⟨ ⟨ g ⟩ ⟩ x)) since reductive (either (reduce) (reduce)))


-- product : A ⨯ (B ⨿ C) ∼ (A ⨯ B ⨿ A ⨯ C)
-- coproduct: ⨿


-- ∏
-- U+221x 	∐
-- ⨅ 	⨆
-- ∏⨿ 
-- ⊓ 	⊔ 	
-- ⨯ 

-- ∐ ■union

-- x∐y
-- ⊔ba \sqcup b if your fonts don't include ‘⨿\amalg

  -- private
  --   π₀ : 




