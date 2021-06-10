
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.Bool.Base where
--

module Verification.Conventions.Prelude.Data.Bool.Base where

open import Verification.Conventions.Proprelude.CubicalConventions
open import Verification.Conventions.Prelude.Classes.Discrete
open import Verification.Conventions.Prelude.Classes.EquivalenceRelation
open import Verification.Conventions.Prelude.Data.StrictId
open import Verification.Conventions.Prelude.Data.Sum
open import Verification.Conventions.Proprelude


-- open import Cubical.Core.Everything

-- open import Cubical.Foundations.Prelude

-- open import Cubical.Data.Empty
-- open import Cubical.Data.Sum.Base

-- open import Cubical.Relation.Nullary
-- open import Cubical.Relation.Nullary.DecidableEq

-- Obtain the booleans
open import Agda.Builtin.Bool public

private
  variable
    -- ℓ : Level
    A : Type ℓ

infixr 6 _and_
infixr 5 _or_
infix  0 if_then_else_

not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
false or false = false
false or true  = true
true  or false = true
true  or true  = true

_and_ : Bool → Bool → Bool
false and false = false
false and true  = false
true  and false = false
true  and true  = true

-- xor / mod-2 addition
_⊕_ : Bool → Bool → Bool
false ⊕ x = x
true  ⊕ x = not x

if_then_else_ : Bool → A → A → A
if true  then x else y = x
if false then x else y = y

_≟_ : Discrete Bool
false ≟ false = yes refl
false ≟ true  = no λ ()
-- λ p →  (λ b → if b then 𝟘-𝒰 else Bool) p true
true  ≟ false = no λ ()
-- λ p → subst (λ b → if b then Bool else 𝟘-𝒰) p true
true  ≟ true  = yes refl

Dec→Bool : Decision A → Bool
Dec→Bool (yes p) = true
Dec→Bool (no ¬p) = false

dichotomyBool : (x : Bool) → (x ≡ true) +-𝒰 (x ≡ false)
dichotomyBool true  = left refl
dichotomyBool false = right refl

-- TODO: this should be uncommented and implemented using instance arguments
-- _==_ : {dA : Discrete A} → A → A → Bool
-- _==_ {dA = dA} x y = Dec→Bool (dA x y)
