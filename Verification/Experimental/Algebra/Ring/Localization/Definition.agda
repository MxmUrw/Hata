
module Verification.Experimental.Algebra.Ring.Localization.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition

-- Multiplicatively closed set

record isMCS {𝑖 : 𝔏 ^ 2} (R : CRing 𝑖) (A : 𝒫 ⟨ R ⟩ :& isSubsetoid) : 𝒰 𝑖 where
  field closed-⋅ : ∀{a b : ⟨ R ⟩} -> a ∈ A -> b ∈ A -> (a ⋅ b) ∈ ⟨ A ⟩
  field closed-⨡ : ⨡ ∈ A
open isMCS {{...}} public

MCS : CRing 𝑖 -> 𝒰 _
MCS R = 𝒫 ⟨ R ⟩ :& isSubsetoid :& isMCS R

module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} where
  record hasNotZero-MCS (M : MCS R) : 𝒰 𝑖 where
    field isNotZero-MCS : ∀{a : ⟨ R ⟩} -> a ∈ M -> a ≁ ◌

  open hasNotZero-MCS {{...}} public

-- record Localize {𝑖 : 𝔏 ^ 2} (R : CRing 𝑖) (M : MCS R) : 𝒰 𝑖 where
--   no-eta-equality
--   pattern
--   constructor _/_
--   field loc↑ : ⟨ R ⟩
--   field loc↓ : ⦋ ⟨ M ⟩ ⦌
-- open Localize public

data Localize {𝑖 : 𝔏 ^ 2} (R : CRing 𝑖) (M : MCS R) : 𝒰 𝑖 where
  _/_ : ⟨ R ⟩ -> ⦋ ⟨ M ⟩ ⦌ -> Localize R M

module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} {M : MCS R} where
  loc↑ : Localize R M -> ⟨ R ⟩
  loc↑ (a / b) = a

  loc↓ : Localize R M -> ⦋ ⟨ M ⟩ ⦌
  loc↓ (a / b) = b

module _ {𝑖 : 𝔏 ^ 2} {R : 𝒰 _} {M : 𝒫 R} {{_ : CRing 𝑖 on R}} {{_ : MCS ′ R ′ on M}} where
  _⋅-MCS_ : ⦋ M ⦌ -> ⦋ M ⦌ -> ⦋ M ⦌
  _⋅-MCS_ (a ∢ aP) (b ∢ bP) = ((a ⋅ b) ∢ closed-⋅ aP bP)
  ⨡-MCS : ⦋ M ⦌
  ⨡-MCS = ⨡ ∢ closed-⨡

module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} {M : MCS R} where
  embed-Localize : ⟨ R ⟩ -> Localize R M
  embed-Localize r = r / ⨡-MCS

