
module Verification.Experimental.Algebra.Ring.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
open import Verification.Experimental.Algebra.Abelian.Definition


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

  assoc-r-⋅ : ∀{a b c : R} -> a ⋅ (b ⋅ c) ∼ a ⋅ b ⋅ c
  assoc-r-⋅ = assoc-l-⋅ ⁻¹

  reduce-⋅◌-r : ∀{a : R} -> a ⋅ ◌ ∼ ◌
  reduce-⋅◌-r {a} =
    let P : a ⋅ ◌ ⋆ a ⋅ ◌ ∼ a ⋅ ◌ ⋆ ◌
        P = a ⋅ ◌ ⋆ a ⋅ ◌     ≣⟨ distr-l-⋅ ⁻¹ ⟩
            a ⋅ (◌ ⋆ ◌)      ≣⟨ refl `cong-⋅` unit-r-⋆ ⟩
            a ⋅ ◌            ≣⟨ unit-r-⋆ ⁻¹ ⟩
            a ⋅ ◌ ⋆ ◌        ∎
    in cancel-⋆-l P

  reduce-⋅◌-l : ∀{a : R} -> ◌ ⋅ a ∼ ◌
  reduce-⋅◌-l {a} =
    let P : ◌ ⋅ a ⋆ ◌ ⋅ a ∼ ◌ ⋅ a ⋆ ◌
        P = ◌ ⋅ a ⋆ ◌ ⋅ a ≣⟨ distr-r-⋅ ⁻¹ ⟩
            (◌ ⋆ ◌) ⋅ a   ≣⟨ unit-r-⋆ `cong-⋅` refl ⟩
            ◌ ⋅ a         ≣⟨ unit-r-⋆ ⁻¹ ⟩
            ◌ ⋅ a ⋆ ◌     ∎
    in cancel-⋆-l P

  switch-◡-⋅-l : ∀{a b : R} -> ◡ (a ⋅ b) ∼ ◡ a ⋅ b
  switch-◡-⋅-l {a} {b} =
    let P₀ : (a ⋅ b) ⋆ (◡ a ⋅ b) ∼ ◌
        P₀ = (a ⋅ b) ⋆ (◡ a ⋅ b) ≣⟨ distr-r-⋅ ⁻¹ ⟩
             (a ⋆ ◡ a) ⋅ b       ≣⟨ inv-r-⋆ `cong-⋅` refl ⟩
             ◌ ⋅ b              ≣⟨ reduce-⋅◌-l ⟩
             ◌                  ∎
    in unique-inverse-⋆-r P₀

  switch-◡-⋅-r : ∀{a b : R} -> ◡ (a ⋅ b) ∼ a ⋅ ◡ b
  switch-◡-⋅-r {a} {b} =
    let P₀ : (a ⋅ b) ⋆ (a ⋅ ◡ b) ∼ ◌
        P₀ = (a ⋅ b) ⋆ (a ⋅ ◡ b)    ≣⟨ distr-l-⋅ ⁻¹ ⟩
             a ⋅ (b ⋆ ◡ b)         ≣⟨ refl `cong-⋅` inv-r-⋆ ⟩
             a ⋅ ◌                 ≣⟨ reduce-⋅◌-r ⟩
             ◌                     ∎
    in unique-inverse-⋆-r P₀

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


