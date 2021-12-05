
module Verification.Core.Theory.Computation.Question.Construction.Exponential where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Question.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Theory.Computation.Question.Construction.Product
open import Verification.Core.Theory.Computation.Question.Construction.MonoidalProduct

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

