
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

-- Natural number literals for β

open import Agda.Builtin.Nat renaming (Nat to β)

instance
  instanceof:π : π-π°
  instanceof:π = tt

instance
  fromNatβ : HasFromNat β
  fromNatβ = record { Constraint = Ξ» _ β π-π° ; fromNat = Ξ» n β n }

