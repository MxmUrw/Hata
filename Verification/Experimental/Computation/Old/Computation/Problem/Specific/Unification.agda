
module Verification.Experimental.Theory.Computation.Problem.Specific.Unification where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Order.Preorder
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition
open import Verification.Experimental.Theory.Computation.Problem.Specific.Forall
open import Verification.Experimental.Theory.Computation.Problem.Specific.Coequalizer




module Unify where
  toForall : ∀ {𝑖 : 𝔏 ^ 3} -> UNIFY 𝑖 -> FORALL _
  toForall (unifyP 𝒞) = forallP (Pair {𝒞 = 𝒞}) hasUnification

  instance
    isDeductive:toForall : ∀{𝑖 : 𝔏 ^ 3} -> isDeductive (UNIFY 𝑖) (FORALL _) toForall
    isDeductive:toForall = deductive (incl (λ x a → x a))




