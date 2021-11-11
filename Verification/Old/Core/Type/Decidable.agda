
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Type.Decidable where

open import Verification.Conventions
open import Verification.Old.Core.Category.EpiMono
open import Verification.Old.Core.Category.Instance.Type

-- Decision : 𝒰 𝑖 -> 𝒰 𝑖
-- Decision A = (A -> 𝟘-𝒰) +-𝒰 A

record IDec (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field decide : Decision A

open IDec {{...}} public

infixr 10 _？
_？ : (A : 𝒰 𝑖) {{_ : IDec A}} -> Decision A
_？ A = decide

rep : ∀{A : 𝒰 𝑖} -> A -> (Lift {j = 𝑖} 𝟙-𝒰 -> A)
rep a = λ _ -> a

isInjective : ∀{A B : 𝒰 𝑖} {f : A -> B} {{_ : IMono f}} -> ∀(a b : A) -> (f a ≡ f b) -> a ≡ b
isInjective a b r = λ i -> isMono (rep a) (rep b) (funExt (λ _ -> r)) i (lift tt)


module _ {A B : 𝒰 𝑖} (f : A -> B) {{_ : IMono f}} where
  inside : ∀{a b : A} -> Decision (a ≡ b) -> Decision (f a ≡ f b)
  inside {a = a} {b} (no x) = no (λ r -> x (isInjective a b r))
  inside (yes x) = yes (cong f x)

  -- inside : ∀{a b : A} -> IDec (a ≡ b) -> IDec (f a ≡ f b)
  -- IDec.decide (inside d) = inside' (decide {{d}})

record IDiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field {{Impl}} : ∀{a b : A} -> IDec (a ≡ b)

record IDiscreteStr (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _≟-Str_ : (a b : A) -> Decision (a ≡-Str b)
open IDiscreteStr {{...}} public


