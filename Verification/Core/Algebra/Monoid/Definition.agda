
module Verification.Core.Algebra.Monoid.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Definition


-- #Notation/Rewrite# ◌ = \Circle

-- [Definition]
-- | A setoid |A| is a /monoid/, that is, the type [..] is inhabited,
--   if the following data is given.
record isMonoid {𝑗 : 𝔏 ^ 2} (A : Setoid 𝑗) : 𝒰 (𝑗) where

  -- | 1. A binary operation [..].
  field _⋆_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩

  -- | 2. A specified element [..].
        ◌ : ⟨ A ⟩

  -- | 3. Proofs that |⋆| is associative,
  --      and |◌| is a unit for it.
        unit-l-⋆   : ∀ {a} -> ◌ ⋆ a ∼ a
        unit-r-⋆   : ∀ {a} -> a ⋆ ◌ ∼ a
        assoc-l-⋆  : ∀ {a b c} -> (a ⋆ b) ⋆ c ∼ a ⋆ (b ⋆ c)

  -- | 4. Finally, a proof that the operation is compatible
  --      with the equivalence relation.
        _≀⋆≀_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆ b₀ ∼ a₁ ⋆ b₁

  -- | We further write [] [..].
  assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
  assoc-r-⋆ = assoc-l-⋆ ⁻¹

  infixl 50 _⋆_ _≀⋆≀_
open isMonoid {{...}} public

-- //

-- [Hide]

Monoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Monoid 𝑗 = Setoid 𝑗 :& isMonoid

module _ {A : 𝒰 _} {{Ap : A is Monoid 𝑖}} where
  macro
   ⋆⃨ : SomeStructure
   ⋆⃨ = #structureOn (λ₋ {A = A} {B = A} {C = A} (_⋆_))


record isCommutative {𝑗 : 𝔏 ^ 2} (A : Monoid 𝑗) : 𝒰 𝑗 where
  field comm-⋆ : ∀{a b : ⟨ A ⟩} -> a ⋆ b ∼ b ⋆ a

open isCommutative {{...}} public


record isSubmonoid {𝑗 : 𝔏 ^ 2} {A} {{_ : Monoid 𝑗 on A}} (P : 𝒫 A :& isSubsetoid) : 𝒰 𝑗 where
  field closed-◌ : ◌ ∈ P
        closed-⋆ : ∀{a b : A} -> a ∈ P -> b ∈ P -> (a ⋆ b) ∈ P
        --⟨ ⟨ P ⟩ a ⟩ -> ⟨ ⟨ P ⟩ b ⟩ -> ⟨ ⟨ P ⟩ (a ⋆ b) ⟩
open isSubmonoid {{...}} public


Submonoid : (M : Monoid 𝑖) -> 𝒰 _
Submonoid M = _ :& isSubmonoid {A = ⟨ M ⟩}

module _ (A : Monoid 𝑖) (B : Monoid 𝑗) where
  record isMonoidHom (f : SetoidHom ′ ⟨ A ⟩ ′ ′ ⟨ B ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where
    field pres-◌ : ⟨ f ⟩ ◌ ∼ ◌
    field pres-⋆ : ∀{a b : ⟨ A ⟩} -> ⟨ f ⟩ (a ⋆ b) ∼ ⟨ f ⟩ a ⋆ ⟨ f ⟩ b

  MonoidHom : 𝒰 _
  MonoidHom = _ :& isMonoidHom

open isMonoidHom {{...}} public

module _ {A : Monoid 𝑖} {B : Monoid 𝑗} where

  instance
    isSetoid:MonoidHom : isSetoid (MonoidHom A B)
    isSetoid:MonoidHom = isSetoid:FullSubsetoid (_ since isSetoid:SetoidHom) (λ f -> ↳ f)

-- //



