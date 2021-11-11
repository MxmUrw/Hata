
module Verification.Core.Algebra.Ring.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition

module AbelianMonoidNotation where
  infixl 50 _+_
  infix 100 -_
  _+_ = _⋆_
  -_ = ◡_

open AbelianMonoidNotation

record isSemiring {𝑗 : 𝔏 ^ 2} (A : Monoid 𝑗 :& isCommutative) : 𝒰 𝑗 where
  field _⋅_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        ⨡ : ⟨ A ⟩
        unit-l-⋅ : ∀{a} -> ⨡ ⋅ a ∼ a
        unit-r-⋅ : ∀{a} -> a ⋅ ⨡ ∼ a
        assoc-l-⋅ : ∀{a b c} -> (a ⋅ b) ⋅ c ∼ a ⋅ (b ⋅ c)
        distr-l-⋅ : ∀{a b c : ⟨ A ⟩} -> a ⋅ (b ⋆ c) ∼ a ⋅ b ⋆ a ⋅ c
        distr-r-⋅ : ∀{a b c : ⟨ A ⟩} -> (b ⋆ c) ⋅ a ∼ b ⋅ a ⋆ c ⋅ a
        _`cong-⋅`_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋅ b₀ ∼ a₁ ⋅ b₁
  _≀⋅≀_ = _`cong-⋅`_
  infixl 80 _⋅_ _`cong-⋅`_ _≀⋅≀_
open isSemiring {{...}} public

Semiring : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Semiring 𝑗 = (Monoid 𝑗 :& isCommutative) :& isSemiring


record isRing {𝑗 : 𝔏 ^ 2}(A : Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup) : 𝒰 𝑗 where

Ring : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Ring 𝑗 = (Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup) :& isRing

-- instance
--   isRing:Any : ∀{A : Monoid 𝑗 :& (isCommutative :> isSemiring) :, isGroup} -> isRing A
--   isRing:Any = record {}

record isCRing {𝑗 : 𝔏 ^ 2} (R : Ring 𝑗) : 𝒰 𝑗 where
  field comm-⋅ : ∀{a b : ⟨ R ⟩} -> a ⋅ b ∼ b ⋅ a
open isCRing {{...}} public

CRing : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
CRing 𝑗 = (Ring 𝑗) :& isCRing

module _ {𝑗 : 𝔏 ^ 2} {R : 𝒰 _} {{_ : Ring 𝑗 on R}} where
-- module _ {𝑗 : 𝔏 ^ 2} {R' : Ring 𝑗} where
--   private
--     R = ⟨ R' ⟩

  infix 200 _²
  _² : R -> R
  _² a = a ⋅ a

  assoc-r-⋅ : ∀{a b c : R} -> a ⋅ (b ⋅ c) ∼ a ⋅ b ⋅ c
  assoc-r-⋅ = assoc-l-⋅ ⁻¹

  reduce-⋅◌-r : ∀{a : R} -> a ⋅ ◌ ∼ ◌
  reduce-⋅◌-r {a} = cancel-⋆-l P
    where P : a ⋅ ◌ ⋆ a ⋅ ◌ ∼ a ⋅ ◌ ⋆ ◌
          P = a ⋅ ◌ ⋆ a ⋅ ◌     ≣⟨ distr-l-⋅ ⁻¹ ⟩
              a ⋅ (◌ ⋆ ◌)      ≣⟨ refl `cong-⋅` unit-r-⋆ ⟩
              a ⋅ ◌            ≣⟨ unit-r-⋆ ⁻¹ ⟩
              a ⋅ ◌ ⋆ ◌        ∎

  reduce-⋅◌-l : ∀{a : R} -> ◌ ⋅ a ∼ ◌
  reduce-⋅◌-l {a} = cancel-⋆-l P
    where P : ◌ ⋅ a ⋆ ◌ ⋅ a ∼ ◌ ⋅ a ⋆ ◌
          P = ◌ ⋅ a ⋆ ◌ ⋅ a ≣⟨ distr-r-⋅ ⁻¹ ⟩
              (◌ ⋆ ◌) ⋅ a   ≣⟨ unit-r-⋆ `cong-⋅` refl ⟩
              ◌ ⋅ a         ≣⟨ unit-r-⋆ ⁻¹ ⟩
              ◌ ⋅ a ⋆ ◌     ∎

  switch-◡-⋅-l : ∀{a b : R} -> ◡ (a ⋅ b) ∼ ◡ a ⋅ b
  switch-◡-⋅-l {a} {b} = unique-inverse-⋆-r P₀
    where P₀ : (a ⋅ b) ⋆ (◡ a ⋅ b) ∼ ◌
          P₀ = (a ⋅ b) ⋆ (◡ a ⋅ b) ≣⟨ distr-r-⋅ ⁻¹ ⟩
              (a ⋆ ◡ a) ⋅ b       ≣⟨ inv-r-⋆ `cong-⋅` refl ⟩
              ◌ ⋅ b              ≣⟨ reduce-⋅◌-l ⟩
              ◌                  ∎

  switch-◡-⋅-r : ∀{a b : R} -> ◡ (a ⋅ b) ∼ a ⋅ ◡ b
  switch-◡-⋅-r {a} {b} = unique-inverse-⋆-r P₀
    where P₀ : (a ⋅ b) ⋆ (a ⋅ ◡ b) ∼ ◌
          P₀ = (a ⋅ b) ⋆ (a ⋅ ◡ b)    ≣⟨ distr-l-⋅ ⁻¹ ⟩
              a ⋅ (b ⋆ ◡ b)         ≣⟨ refl `cong-⋅` inv-r-⋆ ⟩
              a ⋅ ◌                 ≣⟨ reduce-⋅◌-r ⟩
              ◌                     ∎

module _ {𝑗 : 𝔏 ^ 2} {R : 𝒰 _} {{_ : CRing 𝑗 on R}} where
  binomial-2 : ∀{a b : R} -> (a + b)² ∼ a ² + ((⨡ + ⨡) ⋅ (a ⋅ b)) + b ²
  binomial-2 {a} {b} =
    (a + b) ⋅ (a + b)                        ⟨ distr-l-⋅ ⟩-∼
    (a + b) ⋅ a + (a + b) ⋅ b                ⟨ distr-r-⋅ ≀⋆≀ distr-r-⋅ ⟩-∼
    (a ² + b ⋅ a) + (a ⋅ b + b ²)            ⟨ assoc-r-⋆ ⟩-∼
    (a ² + b ⋅ a) + a ⋅ b + b ²              ⟨ assoc-l-⋆ ≀⋆≀ refl ⟩-∼
    a ² + (b ⋅ a + a ⋅ b) + b ²              ⟨ refl ≀⋆≀ (comm-⋅ ≀⋆≀ refl) ≀⋆≀ refl ⟩-∼
    a ² + (a ⋅ b + a ⋅ b) + b ²              ⟨ refl ≀⋆≀ (unit-l-⋅ ⁻¹ ≀⋆≀ unit-l-⋅ ⁻¹) ≀⋆≀ refl ⟩-∼
    a ² + (⨡ ⋅ (a ⋅ b) + ⨡ ⋅ (a ⋅ b)) + b ²   ⟨ refl ≀⋆≀ (distr-r-⋅ ⁻¹) ≀⋆≀ refl ⟩-∼
    a ² + ((⨡ + ⨡) ⋅ (a ⋅ b)) + b ²          ∎


--------------------------------------------------------------------------------
-- Ideals


-- record isIdeal {A} {{_ : Ring 𝑗 on A}} (P : 𝒫 A :& isSubsetoid :& isSubmonoid :& isSubgroup :& isSubabelian {A = ′ A ′}) : 𝒰 𝑗 where
record isIdeal {𝑗 : 𝔏 ^ 2} {A : Ring 𝑗} (P : 𝒫 ⟨ A ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup :& isSubabelian {A = ′ ⟨ A ⟩ ′}) : 𝒰 𝑗 where
  field ideal-l-⋅ : ∀{a b} -> ⟨ ⟨ P ⟩ b ⟩ -> ⟨ ⟨ P ⟩ (a ⋅ b) ⟩
        ideal-r-⋅ : ∀{a b} -> ⟨ ⟨ P ⟩ a ⟩ -> ⟨ ⟨ P ⟩ (a ⋅ b) ⟩
open isIdeal {{...}} public

Ideal : (R : Ring 𝑗) -> 𝒰 _
Ideal R = Subabelian ′ ⟨ R ⟩ ′ :& isIdeal {A = R}

module _ {𝑗 : 𝔏 ^ 2} {R : Ring 𝑗} where
  RelIdeal : Ideal R -> ⟨ R ⟩ -> ⟨ R ⟩ -> 𝒰 _
  RelIdeal I = RelSubgroup ′ ⟨ I ⟩ ′



record isPrime {𝑗 : 𝔏 ^ 2} {R : Ring 𝑗} (I : Ideal R) : 𝒰 𝑗 where
  field prime : ∀{a b} -> ⟨ ⟨ I ⟩ (a ⋅ b) ⟩ -> ⟨ ⟨ I ⟩ a ⟩ +-𝒰 ⟨ ⟨ I ⟩ b ⟩


{-
-}


