
module Verification.Experimental.Data.Real.Application.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Ring.Localization
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.DedekindCompletion.Definition3
open import Verification.Experimental.Order.DedekindCompletion.Instance.Ring
-- open import Verification.Experimental.Order.DedekindCompletion.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Experimental.Data.Real.Definition

open import Application.Definition

instance
  Show:ℤ : IShow ℤ
  IShow.show Show:ℤ (pos n) = show n
  IShow.show Show:ℤ (negsuc n) = "-" <> show (suc n)

instance
  Show:ℚ : IShow ℚ
  IShow.show Show:ℚ (a / (b ∢ _)) = show a <> "/" <> show b

mynumber : ℝ
mynumber =
  let z = 2
      q : ℚ
      q = embed-Localize z
      r : ℝ
      r = return-Cut _ q
  in r


approx-ℝ-impl : ℕ -> (r : ℝ) -> (q : ℚ) -> q ∈ (⩘ r) -> List ℚ -> List ℚ
approx-ℝ-impl zero r q qp qs = qs
approx-ℝ-impl (suc n) r q qp qs =
  let (q' ∢ q'p) , _ = open-⩘ qp
  in approx-ℝ-impl n r (q') q'p (qs <> (q ∷ []))

approx-ℝ : ℕ -> ℝ -> List ℚ
approx-ℝ n r = approx-ℝ-impl n r _ (inhabited-⩘ .Proof) []


doapp : List ℚ
doapp = approx-ℝ 20 mynumber

realapp : Application
realapp = execute "real" (λ _ -> show doapp)

