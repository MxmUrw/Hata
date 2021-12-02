
module Verification.Conventions.Prelude.Classes.Setoid where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes.Operators.Unary
-- open import Verification.Conventions.Prelude.Classes.Cast
-- open import Verification.Conventions.Prelude.Classes.Anything
open import Verification.Conventions.Prelude.Data.StrictId


-- #Notation/Annotatable# trans
-- #Notation/SemanticCategory# \mathrm{Eqv} = Equiv

-- [Definition]
-- | We call a type |A| a /setoid/ if it is equipped with an
--   equivalence relation.
--   That is, the type [..] is constructed by giving the following data.
record isSetoid {𝑗 𝑖 : 𝔏} (A : 𝒰 𝑖) : 𝒰 (𝑖 ⊔ 𝑗 ⁺) where
  constructor isSetoid:byDef

  -- | 1. A binary relation [..].
  field _∼_ : A -> A -> 𝒰 𝑗

  -- | 2. Proofs of reflexivity, symmetry, and transitivity.
        refl  : ∀ {a : A} -> a ∼ a
        sym   : ∀ {a b : A} -> a ∼ b -> b ∼ a
        _∙_   : ∀ {a b c : A} -> a ∼ b -> b ∼ c -> a ∼ c

  -- |: For convenience, we say [] [..].
  _≁_ : A -> A -> 𝒰 (𝑗)
  a ≁ b = ¬ a ∼ b

  -- |> And we usually write |a ⁻¹| for |sym a|.

  infixl 30 _∙_
-- //
open isSetoid {{...}} public


-- [Hide]
module _ {X : 𝒰 𝑗} {{_ : isSetoid {𝑖} X}} where
  open import Verification.Conventions.Prelude.Data.StrictId
  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x ∼ y) (y ∼ x)
    Notation-Inverse:Equiv Notation-Inverse.⁻¹ = sym
-- //


-- aa[Example]
-- a| Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- a| Then the identity type on |A| is symmetric.
  sym-≣ : ∀{a b : A} -> a ≣ b -> b ≣ a
  sym-≣ refl-≣ = refl-≣

  -- a| And it is transitive.
  _∙-≣_ : ∀{a b c : A} -> a ≣ b -> b ≣ c -> a ≣ c
  _∙-≣_ refl-≣ q = q

  -- a| This means that a type |A| together with the identity type
  --   is a setoid.
  isSetoid:byId : isSetoid A
  isSetoid:byId = isSetoid:byDef _≣_ refl-≣ sym-≣ _∙-≣_
-- a//


module _ {X : 𝒰 𝑖} where
  isSetoid:byPath : isSetoid X
  isSetoid:byPath = isSetoid:byDef _≡_ refl-Path sym-Path trans-Path

  isSetoid:byStrId : isSetoid X
  isSetoid:byStrId = isSetoid:byId



