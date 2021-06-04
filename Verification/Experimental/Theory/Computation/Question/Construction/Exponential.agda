
module Verification.Experimental.Theory.Computation.Question.Construction.Exponential where

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
open import Verification.Experimental.Theory.Computation.Question.Construction.MonoidalProduct

module _ {𝔓 𝔔 : Question (𝑖 , 𝑗)} where

  instance
    isQuestion:Reduction : isQuestion _ (Reduction 𝔓 𝔔)
    isQuestion:Reduction = answerWith (λ f → ∑ λ (a : ⟨ 𝔓 ⟩) -> ⟨ f ⟩ a ‽)


_⇒_ : (𝔓 𝔔 : Question (𝑖 , 𝑗)) -> Question _
_⇒_ 𝔓 𝔔 = ′ Reduction 𝔓 𝔔 ′


module _ {𝔓 𝔔 : Question (𝑖 , 𝑖)} where
  unit : 𝔓 ⟶ (𝔔 ⇒ (𝔓 ⊗ 𝔔))
  unit = incl ((λ p → ((λ q → (p , q)) since reductive (λ x → snd x)))
    since reductive (λ (_ , q , _) → q))

  counit : (𝔓 ⊗ (𝔓 ⇒ 𝔔)) ⟶ 𝔔
  counit = incl ((λ (x , f) → ⟨ f ⟩ x) since reductive (λ {(p , f)} x → reduce x , (p , x)))


-- ─⊗ 

