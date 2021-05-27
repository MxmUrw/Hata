
module Verification.Experimental.Algebra.Ring.Localization.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition

-- Multiplicatively closed set

record isMCS (R : CRing 𝑖) (A : 𝒫 ⟨ R ⟩ :& isSubsetoid) : 𝒰 𝑖 where
  field closed-⋅ : ∀{a b} -> ⟨ A ⟩ a -> ⟨ A ⟩ b -> ⟨ A ⟩ (a ⋅ b)
  field closed-⨡ : ⟨ A ⟩ ⨡
open isMCS {{...}} public

MCS : CRing 𝑖 -> 𝒰 _
MCS R = 𝒫 ⟨ R ⟩ :& isSubsetoid :& isMCS R

module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} where
  record hasNotZero-MCS (M : MCS R) : 𝒰 𝑖 where
    field isNotZero-MCS : ∀{a : ⟨ R ⟩} -> ⟨ M ⟩ a -> a ≁ ◌

  open hasNotZero-MCS {{...}} public

record Localize (R : CRing 𝑖) (M : MCS R) : 𝒰 𝑖 where
  constructor _/_
  field loc↑ : ⟨ R ⟩
  field loc↓ : ⦋ ⟨ M ⟩ ⦌
open Localize public

module _ {R : 𝒰 _} {M : 𝒫 R} {{_ : CRing 𝑖 on R}} {{_ : MCS ′ R ′ on M}} where
  _⋅-MCS_ : ⦋ M ⦌ -> ⦋ M ⦌ -> ⦋ M ⦌
  _⋅-MCS_ (a ∈ aP) (b ∈ bP) = (a ⋅ b ∈ closed-⋅ aP bP)
  ⨡-MCS : ⦋ M ⦌
  ⨡-MCS = ⨡ ∈ closed-⨡


