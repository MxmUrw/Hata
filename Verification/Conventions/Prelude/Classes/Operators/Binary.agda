

module Verification.Conventions.Prelude.Classes.Operators.Binary where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Data.Maybe

-- Convention: we call these record "DirectSum-Notation" or "Index-Notation"
-- TODO: apply convention

record INotation:DirectSum (A : 𝒰 𝑖) : (𝒰 𝑖) where
  field _⊕_ : A -> A -> A
open INotation:DirectSum {{...}} public

record INotation:Union (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _∪_ : A -> A -> A
        ∅ : A
open INotation:Union {{...}} public

--------------------------------------------------------------------
-- Restriction

record Notation-Restriction (A : 𝒰 𝑖) (B : 𝒰 𝑗) (C : A -> B -> 𝒰 𝑘) : (𝒰 (𝑖 ⊔ 𝑗 ⊔ 𝑘)) where
  field _∣_ : (a : A) -> (b : B) -> C a b
  infix 90 _∣_

open Notation-Restriction {{...}} public


--------------------------------------------------------------------
-- ====* Accessing tuples


-- private
--   resolve : ∀{A : 𝒰 𝑖} -> (Maybe (A -> 𝒰 𝑗)) -> A -> 𝒰 𝑗
--   resolve (left x) = IAnything
--   resolve (right x) = x


record Index-Notation (X : 𝒰 𝑖) (Idx : X -> 𝒰 𝑗) (Pred : (∀{x} -> Idx x -> 𝒰 𝑙)) (Res : (∑ Idx) -> 𝒰 𝑘) : 𝒰 (𝑗 ⊔ 𝑖 ⊔ 𝑘 ⊔ 𝑙) where
  field _⌄_ : (x : X) -> (i : Idx x) -> {{_ : Pred i}} -> Res (x , i)
  infix 150 _⌄_
open Index-Notation {{...}} public


record Exponent-Notation (X : 𝒰 𝑖) (Idx : 𝒰 𝑗) (Res : (X ×-𝒰 Idx) -> 𝒰 𝑘) : 𝒰 (𝑗 ⊔ 𝑖 ⊔ 𝑘) where
  field _^_ : (x : X) -> (i : Idx) -> Res (x , i)
  infix 150 _^_
open Exponent-Notation {{...}} public
