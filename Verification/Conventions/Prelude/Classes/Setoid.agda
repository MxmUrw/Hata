
module Verification.Conventions.Prelude.Classes.Setoid where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes.Operators.Unary
-- open import Verification.Conventions.Prelude.Classes.Cast
-- open import Verification.Conventions.Prelude.Classes.Anything
open import Verification.Conventions.Prelude.Data.StrictId



-- [Definition]
-- | We call a type |A| a /setoid/ if it is equipped with an
--   equivalence relation.
--   That is, the type [..] is constructed by giving the following data.
record isSetoid {๐ ๐ : ๐} (A : ๐ฐ ๐) : ๐ฐ (๐ โ ๐ โบ) where
  constructor isSetoid:byDef

  -- | 1. A binary relation [..].
  field _โผ_ : A -> A -> ๐ฐ ๐

  -- | 2. Proofs of reflexivity, symmetry, and transitivity.
        refl  : โ {a : A} -> a โผ a
        sym   : โ {a b : A} -> a โผ b -> b โผ a
        _โ_   : โ {a b c : A} -> a โผ b -> b โผ c -> a โผ c

  -- |: For convenience, we say [] [..].
  _โ_ : A -> A -> ๐ฐ (๐)
  a โ b = ยฌ a โผ b

  -- |> And we usually write |a โปยน| for |sym a|.

  infixl 30 _โ_
-- //
open isSetoid {{...}} public


-- [Hide]
module _ {X : ๐ฐ ๐} {{_ : isSetoid {๐} X}} where
  open import Verification.Conventions.Prelude.Data.StrictId
  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x โผ y) (y โผ x)
    Notation-Inverse:Equiv Notation-Inverse.โปยน = sym
-- //


-- [Example]
-- | Let [..] be a type.
module _ {A : ๐ฐ ๐} where
  -- |> Then the identity type on |A| is symmetric.
  -- The proof can be done by pattern matching on the
  -- given proof of |a โฃ b|, thus reducing the goal
  -- to |a โฃ a|, which we can conclude by |refl-โฃ|.
  sym-โฃ : {a b : A} -> a โฃ b -> b โฃ a
  sym-โฃ refl-โฃ = refl-โฃ

  -- |> Similarly we can use pattern matching to prove transitivity.
  _โ-โฃ_ : {a b c : A} -> a โฃ b -> b โฃ c -> a โฃ c
  _โ-โฃ_ refl-โฃ q = q

  -- |> This means that |A| together with the identity type
  -- is a setoid.
  isSetoid:byId : isSetoid A
  isSetoid:byId = isSetoid:byDef _โฃ_ refl-โฃ sym-โฃ _โ-โฃ_
-- //

-- [Example]
-- | Let [..] be a type.
module _ {A : ๐ฐ ๐} where
  -- |> Then similarly the path relation |โก : A -> A -> ๐ฐ| makes |A| into a setoid.
  -- The proofs that this is an equivalence relation can be taken from the builtin cubical library.
  isSetoid:byPath : isSetoid A
  isSetoid:byPath = isSetoid:byDef _โก_ refl-Path sym-Path trans-Path
-- //



-- [Hide]

refl-โก = refl-Path
_โ-โก_ = trans-Path
_โปยน-โก_ = sym-Path

module _ {A : ๐ฐ ๐} {{_ : isSetoid {๐} A}} where
  โกโโผ : โ{a b : A} -> a โก b -> a โผ b
  โกโโผ {a} p = transport (ฮป i -> a โผ p i) refl

-- //


