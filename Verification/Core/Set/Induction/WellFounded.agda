
module Verification.Core.Set.Induction.WellFounded where

open import Verification.Conventions hiding (_⊔_)

-- NOTE: This file is a copy from the module Cubical.Induction.WellFounded
--       in the cubical standard library.
--       For technical reasons it is currently reproduced here.

Rel : ∀{ℓ} → 𝒰 ℓ → ∀ ℓ' → 𝒰 _
Rel A ℓ = A → A → 𝒰 ℓ

module _ {ℓ ℓ'} {A : 𝒰 ℓ} (_<_ : A → A → 𝒰 ℓ') where
  WFRec : ∀{ℓ''} → (A → 𝒰 ℓ'') → A → 𝒰 _
  WFRec P x = ∀ y → y < x → P y

  data Acc (x : A) : 𝒰 (ℓ-max ℓ ℓ') where
    acc : WFRec Acc x → Acc x

  WellFounded : 𝒰 _
  WellFounded = ∀ x → Acc x


module _ {ℓ ℓ'} {A : 𝒰 ℓ} {_<_ : A → A → 𝒰 ℓ'} where
  isPropAcc : ∀ x → isProp (Acc _<_ x)
  isPropAcc x (acc p) (acc q)
    = λ i → acc (λ y y<x → isPropAcc y (p y y<x) (q y y<x) i)

  access : ∀{x} → Acc _<_ x → WFRec _<_ (Acc _<_) x
  access (acc r) = r

  private
    wfi : ∀{ℓ''} {P : A → 𝒰 ℓ''}
        → ∀ x → (wf : Acc _<_ x)
        → (∀ x → (∀ y → y < x → P y) → P x)
        → P x
    wfi x (acc p) e = e x λ y y<x → wfi y (p y y<x) e

  module WFI (wf : WellFounded _<_) where
    module _ {ℓ''} {P : A → 𝒰 ℓ''} (e : ∀ x → (∀ y → y < x → P y) → P x) where
      private
        wfi-compute : ∀ x ax → wfi x ax e ≡ e x (λ y _ → wfi y (wf y) e)
        wfi-compute x (acc p)
          = λ i → e x (λ y y<x → wfi y (isPropAcc y (p y y<x) (wf y) i) e)

      induction :  ∀ x → P x
      induction x = wfi x (wf x) e

      induction-compute : ∀ x → induction x ≡ (e x λ y _ → induction y)
      induction-compute x = wfi-compute x (wf x)



