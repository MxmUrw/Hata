
module Verification.Experimental.Meta.Structure2 where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)
open import Verification.Experimental.Order.Lattice

record ∑i_ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field {{ifst}} : A
  field {{isnd}} : B (ifst)
open ∑i_ {{...}} public

record hasU (A : 𝒰 𝑖) 𝑗 𝑘 : 𝒰 (𝑖 ､ 𝑗 ⁺ ､ 𝑘 ⁺) where
  field getU : 𝒰 𝑗
  field getP : getU -> 𝒰 𝑘
  field reconstruct : ∑ getP -> A
open hasU public

record _:&_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑘 ､ 𝑙) where
  constructor make&
  field El : getU U
  field {{oldProof}} : getP U El
  field {{Proof}} : P (reconstruct U (El , oldProof))
open _:&_ {{...}} public hiding (El)
open _:&_ public using (El)

infixl 30 _:&_

record _:,_ {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} (P : UU -> 𝒰 𝑗) (Q : UU -> 𝒰 𝑗₂) (a : UU) : 𝒰 (𝑗 ､ 𝑗₂) where
  constructor make,
  field {{Proof1}} : P a
  field {{Proof2}} : Q a

infixr 80 _:,_

record isAnything {A : 𝒰 𝑖} (a : A) (𝑗 : 𝔏) : 𝒰 (𝑖 ⊔ 𝑗) where

instance
  isAnything:anything : {A : 𝒰 𝑖} {a : A} {𝑗 : 𝔏} -> isAnything a 𝑗
  isAnything:anything = {!!}

-- instance
--   hasU:𝒰 : ∀{𝑖 𝑗 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (𝑖 ⁺ ⊔ 𝑗)
--   getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
--   getP (hasU:𝒰 {𝑖} {𝑗 = 𝑗}) u = isAnything u 𝑗

instance
  hasU:𝒰 : ∀{𝑖 : 𝔏} -> hasU (𝒰 𝑖) (𝑖 ⁺) (𝑖 ⁺)
  getU (hasU:𝒰 {𝑖}) = 𝒰 𝑖
  getP (hasU:𝒰 {𝑖}) u = isAnything u 𝑖
  reconstruct (hasU:𝒰 {𝑖}) (x , _) = x

instance
  hasU:& : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} {P : UU -> 𝒰 𝑗} -> hasU (UU :& P) _ _
  getU (hasU:& {UU = A} {{U}}) = getU U
  getP (hasU:& {UU = A} {{U}} {P = P}) a = ∑i λ (p1 : getP U a) -> P (reconstruct U (a , p1))
  reconstruct (hasU:& {UU = A} {{U}} {P = P}) (a , pa) = make& a -- {{pa .ifst}} {{pa .isnd}}

Just : ∀{A : 𝒰 𝑖} -> (P : A -> 𝒰 𝑗) -> (a : A) -> {{_ : isAnything a 𝑖}} -> 𝒰 𝑗
Just P a = P a

mytest : ∀{𝑖} -> hasU ((𝒰 𝑖) :& isPreorder) _ _
mytest {𝑖 = 𝑖} = hasU:& {_} {{_}} {_}


record isCompleteJoinSemilattice2 (A : 𝒰 𝑖 :& isPreorder) : 𝒰 (𝑖 ⁺) where
  field ⋁ : ∀{X : 𝒰 𝑖} -> (X -> El A) -> El A
        ι-⋁ : ∀{X F} -> ∀ (x : X) -> F x ≤ ⋁ F
        [_]-⋁ : ∀{X F b} -> (∀(x : X) -> F x ≤ b) -> ⋁ F ≤ b
open isCompleteJoinSemilattice2 {{...}} public

record isMeetSemilattice2 (A : 𝒰 𝑖 :& isPreorder) : 𝒰 𝑖 where
  field ⊤ : El A
        initial-⊤ : ∀(a : El A) -> a ≤ ⊤
  field _∧_ : El A -> El A -> El A
        π₀-∧ : {a b : El A} -> a ∧ b ≤ a
        π₁-∧ : {a b : El A} -> a ∧ b ≤ b
        ⟨_,_⟩-∧ : {a b c : El A} -> c ≤ a -> c ≤ b -> c ≤ a ∧ b

  infixl 60 _∧_
open isMeetSemilattice2 {{...}} public


test2 : (𝑖 : 𝔏) -> 𝒰 _
test2 𝑖 =
  let X = _:&_ (𝒰 𝑖 :& isPreorder) {{U = mytest}} isCompleteJoinSemilattice2
  in 𝟘-𝒰

record isFrame (A : 𝒰 𝑖 :& isPreorder :& (isCompleteJoinSemilattice2 :, isMeetSemilattice2)) : 𝒰 (𝑖 ⁺) where
  -- field pp : ∀{a : El A} -> a ≤ a
  field distribute-Frame : ∀{X} {F : X -> El A} {a} -> ⋁ F ∧ a ≚ ⋁ (λ x -> F x ∧ a)

unquoteDecl Frame frame = #struct "Frame" (quote isFrame) "A" Frame frame




