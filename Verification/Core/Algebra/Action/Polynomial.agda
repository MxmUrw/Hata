
module Verification.Core.Algebra.Action.Polynomial where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Category.Instance.Set.Equalizers
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Idempotent
-- open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Homotopy.Level
open import Verification.Core.Order.Totalorder
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
-- open import Verification.Core.Type.Instance.Nat
open import Verification.Core.Type.Instance.Int
open import Verification.Core.Type.Instance.Sum
open import Verification.Core.Type.Decidable

open import Verification.Core.Algebra.Basic.Abelian
open import Verification.Core.Algebra.Basic.Group
open import Verification.Core.Algebra.Basic.Monoid
open import Verification.Core.Algebra.Basic.Ring
open import Verification.Core.Algebra.Action.Combination

open import Verification.Core.Type.Instance.Fin


module _ (R : 𝒰 𝑖) {{_ : IRing R}} (n : ℕ) where
  Polynomial = Combination R (Fin n)



private
  X : Polynomial ℤ 2
  X = ⟨ normalize ⟩ (((pos 1) , (0 , 1 , refl)) ∷ [])

  Y : Polynomial ℤ 2
  Y = ⟨ normalize ⟩ (((pos 1) , (1 , 0 , refl)) ∷ [])


  testp : Polynomial ℤ 2
  testp = X + X + Y + X + (- Y)





