
module Verification.Writing.Introduction-back where

open import Verification.Conventions hiding (_≟_)
open import Verification.Unification.Instance.HMType

₀ : Fin 1
₀ = (0 , 0 , refl)

₁ : Fin 2
₁ = (1 , 0 , refl)

_≟_ : Type -> Type -> 𝟙-𝒰
_≟_ _ _ = tt
