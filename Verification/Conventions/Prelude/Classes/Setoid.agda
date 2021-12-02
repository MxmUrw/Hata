
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


-- [Example]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- |> Then the identity type on |A| is symmetric.
  -- The proof can be done by pattern matching on the
  -- given proof of |a ≣ b|, thus reducing the goal
  -- to |a ≣ a|, which we can conclude by |refl-≣|.
  sym-≣ : {a b : A} -> a ≣ b -> b ≣ a
  sym-≣ refl-≣ = refl-≣

  -- |> Similarly we can use pattern matching to prove transitivity.
  _∙-≣_ : {a b c : A} -> a ≣ b -> b ≣ c -> a ≣ c
  _∙-≣_ refl-≣ q = q

  -- |> This means that |A| together with the identity type
  -- is a setoid.
  isSetoid:byId : isSetoid A
  isSetoid:byId = isSetoid:byDef _≣_ refl-≣ sym-≣ _∙-≣_
-- //

-- [Example]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- |> Then similarly the path relation |≡ : A -> A -> 𝒰| makes |A| into a setoid.
  -- The proofs that this is an equivalence relation can be taken from the builtin cubical library.
  isSetoid:byPath : isSetoid A
  isSetoid:byPath = isSetoid:byDef _≡_ refl-Path sym-Path trans-Path
-- //



