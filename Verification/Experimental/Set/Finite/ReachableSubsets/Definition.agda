
module Verification.Experimental.Set.Finite.ReachableSubsets.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.HeytingAlgebra

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  record isInjective (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
    field injective : ∀ {a b} -> f a ≡-Str f b -> a ≡-Str b

  open isInjective {{...}} public

  Im : (A -> B) -> B -> Prop _
  Im f b = ∣ (∑ λ a -> f a ≡-Str b) ∣


module _ {A : 𝒰 𝑖} where
  record isReachable {P Q : A -> Prop 𝑖} (p : P ≤ Q) : 𝒰 𝑖 where
    constructor isreachable
    field reachSize : ℕ
    -- field reachVec : Vec A reachSize
    field reachMap : Fin-R reachSize -> A
    -- reachMap i = lookup i reachVec
    field {{isInjective:reachMap}} : isInjective reachMap
    field reachEq : P ∨ Im reachMap ∼ Q

  open isReachable public


record isFinite (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field reach : ∀ (p q : 𝒫 A) -> (s : p ≤ q) -> isReachable s
open isFinite {{...}} public

Finite : (𝑖 : 𝔏) -> 𝒰 _
Finite 𝑖 = 𝒰 𝑖 :& isFinite

-- isMonic`from`isInjective a

-- private
--   lem-30 : ∀{A B : 𝒰 𝑖} {P : A +-𝒰 B -> Prop 𝑗} -> P ∼ ((P ∧ left) ∨ (P ∣ right))
--   lem-30 = ?


module _ {A B : 𝒰 _} {{_ : Finite 𝑖 on A}} {{_ : Finite 𝑖 on B}} where
  instance
    isFinite:+ : isFinite (A +-𝒰 B)
    isFinite.reach isFinite:+ P Q s =
      let -- We restrict our subset proof |s| to the left and to the right sides
          -- using |monotone|, and since both |A| and |B| are finite, we get reachability
          -- proofs for them.
          Ap = reach (P ∣ left) (Q ∣ left) (monotone s)
          Bp = reach (P ∣ right) (Q ∣ right) (monotone s)

          -- We call:
          isreachable m u p = Ap
          isreachable n v q = Bp

          -- h : Fin-R (m +-ℕ n) -> (A +-𝒰 B)
          -- h = {!!}
          xx : Fin-R (m +-ℕ n) -> Fin-R m +-𝒰 Fin-R n
          xx = {!!}

          w : Fin-R m +-𝒰 Fin-R n -> A +-𝒰 B
          w = map-+-𝒰 u v

          p' : (P ∣ left) ∨ Im u ∼ (Q ∣ left)
          p' = p


          P₀ : (P ∨ Im w) ∼ Q
          P₀ = {!!}

          P₁ : (P ∨ Im (xx ◆-𝒰 w)) ∼ Q
          P₁ = {!!}


      in record
        { reachSize = m +-ℕ n
        ; reachMap = xx ◆-𝒰 w
        ; isInjective:reachMap = {!!}
        ; reachEq = P₁
        }


