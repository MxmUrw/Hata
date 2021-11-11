
module Verification.Core.Meta.Structure1 where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)
open import Verification.Core.Order.Lattice

record hasU (A : 𝒰 𝑖) 𝑗 𝑘 : 𝒰 (𝑖 ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
  field getU : 𝒰 𝑗
  field getP : getU -> 𝒰 𝑘
open hasU public

record _:&_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : (a : getU U) -> {{_ : getP U a}} -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑙) where
  field El : getU U
  field {{oldProof}} : getP U El
  field {{Proof}} : P El {{oldProof}}
open _:&_ public

data isAnything {A : 𝒰 𝑖} (a : A) (𝑗 : 𝔏) : 𝒰 (𝑖 ⊔ 𝑗) where

instance
  isAnything:anything : {A : 𝒰 𝑖} {a : A} {𝑗 : 𝔏} -> isAnything a 𝑗
  isAnything:anything = {!!}

instance
  hasU:𝒰 : ∀{𝑖 𝑗 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (𝑖 ⁺ ⊔ 𝑗)
  getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
  getP (hasU:𝒰 {𝑖} {𝑗 = 𝑗}) u = isAnything u 𝑗

instance
  hasU:& : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} {P : (a : getU U) -> {{_ : getP U a}} -> 𝒰 𝑗} -> hasU (UU :& P) _ _
  getU (hasU:& {UU = A} {{U}}) = getU U
  getP (hasU:& {UU = A} {{U}} {P = P}) a = ∀{{pp : getP U a}} -> P a

Just : ∀{A : 𝒰 𝑖} -> (P : A -> 𝒰 𝑗) -> (a : A) -> {{_ : isAnything a 𝑖}} -> 𝒰 𝑗
Just P a = P a

mytest : ∀{𝑖} -> hasU (𝒰 𝑖 :& Just isPreorder) _ _
mytest {𝑖 = 𝑖} = hasU:& {_} {{_}} {_}


record isCompleteJoinSemilattice2 (A : 𝒰 𝑖) {{_ : isPreorder A}} : 𝒰 (𝑖 ⁺) where
  field ⋁ : ∀{X : 𝒰 𝑖} -> (X -> A) -> A
        ι-⋁ : ∀{X F} -> ∀ (x : X) -> F x ≤ ⋁ F
        [_]-⋁ : ∀{X F b} -> (∀(x : X) -> F x ≤ b) -> ⋁ F ≤ b
open isCompleteJoinSemilattice2 {{...}} public

test2 : (𝑖 : 𝔏) -> 𝒰 _
test2 𝑖 =
  let X = _:&_ (𝒰 𝑖 :& (Just isPreorder)) {{U = mytest}}
  in {!!}
