
module Verification.Core.Theory.Computation.Problem.Specific.Unification where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Order.Preorder
-- open import Verification.Core.Category.Std.Category.As.Monoid
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
open import Verification.Core.Theory.Computation.Problem.Definition
open import Verification.Core.Theory.Computation.Problem.Specific.Forall
open import Verification.Core.Theory.Computation.Problem.Specific.Coequalizer




module Unify where
  toForall : ∀ {𝑖 : 𝔏 ^ 3} -> UNIFY 𝑖 -> FORALL _
  toForall (unifyP 𝒞) = forallP (Pair {𝒞 = 𝒞}) hasUnification

  instance
    isDeductive:toForall : ∀{𝑖 : 𝔏 ^ 3} -> isDeductive (UNIFY 𝑖) (FORALL _) toForall
    isDeductive:toForall = deductive (incl (λ x a → x a))




