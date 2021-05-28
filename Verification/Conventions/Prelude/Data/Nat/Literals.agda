
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.Nat.Literals where
--

module Verification.Conventions.Prelude.Data.Nat.Literals where

open import Verification.Conventions.Proprelude.CubicalConventions
open import Verification.Conventions.Proprelude

open import Agda.Builtin.FromNat public
  renaming (Number to HasFromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to HasFromNeg)
-- open import Cubical.Data.Unit.Base public

-- Natural number literals for ℕ

open import Agda.Builtin.Nat renaming (Nat to ℕ)

instance
  instanceof:𝟙 : 𝟙-𝒰
  instanceof:𝟙 = tt

instance
  fromNatℕ : HasFromNat ℕ
  fromNatℕ = record { Constraint = λ _ → 𝟙-𝒰 ; fromNat = λ n → n }

