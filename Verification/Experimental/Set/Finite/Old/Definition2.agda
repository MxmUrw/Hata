
module Verification.Experimental.Set.Finite.Definition2 where

open import Verification.Conventions

open import Verification.Experimental.Algebra.Setoid
open import Verification.Experimental.Set.Discrete

record isDec (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field decide : ((¬ A) +-𝒰 A)
open isDec public

Dec : (𝑖 : 𝔏) -> 𝒰 (𝑖 ⁺)
Dec 𝑖 = (𝒰 𝑖) :& isDec


-- module _ {U : 𝒰 𝑖} {{UU : hasU U 𝑗 𝑘}} where
--   _⊆'_ : ∀{A : 𝒰 𝑖} -> (P Q : A -> U) -> 𝒰 _
--   _⊆'_ {A = A} P Q = ∀{a : A} ->
--     let X = destructEl UU (P a) -> 𝒰₀
--     in {!!} -- ∀ {a} -> destructEl UU (P a) -> UU .destructEl (Q a)

  -- _⫗'_ : ∀{A : 𝒰 𝑖} -> (P Q : A -> 𝒰 𝑗) -> 𝒰 _
  -- _⫗'_ P Q = P ⊆ Q ×-𝒰 Q ⊆ P

  -- infix 40 _⊆'_ _⫗'_

module _ {𝑖 : 𝔏} where
  instance
    Setoid:Fun : ∀{A : 𝒰 𝑖} -> isSetoid _ (A -> Dec 𝑗)
    isSetoid.myRel Setoid:Fun P Q = (λ a -> ⟨ P a ⟩) ⫗ (λ a -> ⟨ Q a ⟩)
    isSetoid.isEquivRel:∼ Setoid:Fun = {!!}

  -- accFirst : (A : 𝒰 𝑖) (𝑗 : 𝔏) {{_ : finAcc A 𝑗}} -> A
  -- accFirst A 𝑗 = nextFrom (λ (a : A) -> Lift 𝟘-𝒰) (λ x → {!!}) .fst

  -- record Accessor (𝑗 : 𝔏) (A : 𝒰 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
  --   field ⟨_⟩ : ∀(P : A -> Dec 𝑗) -> (∏ λ a -> ⟨ P a ⟩) +-𝒰 (∑ λ a -> ¬ ⟨ P a ⟩)
  -- open Accessor public

  Accessor : (𝑗 : 𝔏) (A : 𝒰 𝑖) -> 𝒰 (𝑗 ⁺ ､ 𝑖)
  Accessor 𝑗 A = ∀(P : A -> Dec 𝑗) -> (∏ λ a -> ⟨ P a ⟩) +-𝒰 (∑ λ a -> ¬ ⟨ P a ⟩)


  module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where

    private
      step : Accessor 𝑗 A -> (P : A -> Dec 𝑗) -> A -> 𝒰 _
      step Acc P a with Acc P
      ... | left x        = Lift 𝟙-𝒰
      ... | just (b , bP) = (¬ a ≡ b) ×-𝒰 ⟨ P a ⟩

      instance
        isDec:step : ∀{Acc : Accessor 𝑗 A} -> {P : A -> Dec 𝑗} -> ∀{a} -> isDec (step Acc P a)
        isDec:step = {!!}

      step' : Accessor 𝑗 A -> (P : A -> Dec 𝑗) -> A -> Dec _
      step' Acc P a = ′ step Acc P a ′ {{isDec:step {Acc = Acc}}}

    data AccPath (Acc : Accessor 𝑖 A) (P Q : A -> Dec 𝑖) : 𝒰 (𝑖 ⁺) where
      refl-AccPath : P ∼ Q -> AccPath Acc P Q
      step-AccPath : AccPath Acc (step' Acc P) Q -> AccPath Acc P Q

  record isFinite (A : 𝒰 𝑖 :& isDiscrete) : 𝒰 (𝑖 ⁺) where
    field Next : Accessor 𝑖 ⟨ A ⟩
          hasPaths : ∀{P Q : ⟨ A ⟩ -> Dec 𝑖} -> (∀ a -> ⟨ P a ⟩ -> ⟨ Q a ⟩) -> AccPath Next P Q

  open isFinite {{...}} public

Finite : (𝑖 : 𝔏) -> 𝒰 _
Finite 𝑖 = 𝒰 𝑖 :& isDiscrete :& isFinite

instance
  isDiscrete:𝟘 : isDiscrete 𝟘-𝒰
  isDiscrete._≟-Str_ isDiscrete:𝟘 ()

  isDiscrete:𝟙 : isDiscrete 𝟙-𝒰
  isDiscrete._≟-Str_ isDiscrete:𝟙 tt tt = yes refl

  isFinite:𝟘 : isFinite ′ 𝟘-𝒰 ′
  isFinite.Next isFinite:𝟘 P = left (λ ())
  isFinite.hasPaths isFinite:𝟘 {P} {Q} x = refl-AccPath (incl ((λ {a} x₁ → 𝟘-rec a) , (λ {a} x₁ → 𝟘-rec a)))


  isFinite:𝟙 : isFinite ′ 𝟙-𝒰 ′
  isFinite.Next isFinite:𝟙 P with decide (P tt .Proof)
  ... | left x = right (tt , x)
  ... | just x = left (λ {tt -> x})
  isFinite.hasPaths isFinite:𝟙 = {!!}

  isDiscrete:+ : {A B : 𝒰 𝑖} {{_ : isDiscrete A}} {{_ : isDiscrete B}} -> isDiscrete (A +-𝒰 B)
  isDiscrete._≟-Str_ isDiscrete:+ = {!!}

  isFinite:+ : {A B : 𝒰 𝑖} {{_ : (isDiscrete :> isFinite) A}} {{_ : (isDiscrete :> isFinite) B}} -> isFinite ′ A +-𝒰 B ′
  isFinite.Next isFinite:+ P with Next (λ a -> P (left a))
  ... | just (a , aP) = right (left a , aP)
  ... | left ¬A with Next (λ b -> P (right b))
  ... | just (b , bP) = right (right b , bP)
  ... | left ¬B = left (λ {(left a)  -> ¬A a
                          ;(right b) -> ¬B b})
  isFinite.hasPaths isFinite:+ = {!!}




