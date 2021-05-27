
module Verification.Experimental.Set.Finite.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Algebra.Setoid
open import Verification.Experimental.Set.Discrete

record isDec (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field decide : ((¬ A) +-𝒰 A)
open isDec public

Dec : (𝑖 : 𝔏) -> 𝒰 (𝑖 ⁺)
Dec 𝑖 = (𝒰 𝑖) :& isDec

module _ {𝑖 : 𝔏} where
  -- record isNames (N : 𝒰 𝑖) : 𝒰 𝑖 where
  -- data Strategy
  -- record finAcc (A : 𝒰 𝑖) (𝑗 : 𝔏) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
  --   field nextFrom : (P : A -> 𝒰 𝑗) -> (¬ ∏ P) -> (∑ (λ a -> ¬ P a))
  -- open finAcc {{...}} public

  instance
    Setoid:Fun : ∀{A : 𝒰 𝑖} -> isSetoid _ (A -> Dec 𝑗)
    isSetoid.myRel Setoid:Fun P Q = (λ a -> ⟨ P a ⟩) ⫗ (λ a -> ⟨ Q a ⟩)
    isSetoid.isEquivRel:∼ Setoid:Fun = {!!}

  -- accFirst : (A : 𝒰 𝑖) (𝑗 : 𝔏) {{_ : finAcc A 𝑗}} -> A
  -- accFirst A 𝑗 = nextFrom (λ (a : A) -> Lift 𝟘-𝒰) (λ x → {!!}) .fst
  Accessor : (𝑗 : 𝔏) (A : 𝒰 𝑖) -> 𝒰 _
  Accessor 𝑗 A = ∀(P : A -> Dec 𝑗) -> (∏ λ a -> ⟨ P a ⟩) +-𝒰 (∑ λ a -> ¬ ⟨ P a ⟩)

  module _ {𝑗 : 𝔏} {A : 𝒰 𝑖} {{_ : ∀{a b : A} -> isDec (a ≡ b)}} where

    private
      step : Accessor 𝑗 A -> (P : A -> Dec 𝑗) -> A -> 𝒰 _
      step Acc P a with Acc P
      ... | left x        = Lift 𝟙-𝒰
      ... | just (b , bP) = (¬ a ≡ b) ×-𝒰 ⟨ P a ⟩

      instance
        isDec:step : ∀{Acc : Accessor 𝑗 A} -> {P : A -> Dec 𝑗} -> ∀{a} -> isDec (step Acc P a)
        isDec:step = ?

    data AccPath (Acc : Accessor 𝑗 A) (P Q : A -> Dec 𝑗) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
      refl-AccPath : P ∼ Q -> AccPath Acc P Q
      step-AccPath : AccPath Acc (λ a -> ′ step Acc P a ′) Q -> AccPath Acc P Q

  record isFinite (𝑗 : 𝔏) (A : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
    field nextFrom : Accessor 𝑗 A

