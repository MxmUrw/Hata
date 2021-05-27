
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.OtherPrimitives where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.Nat

open import Agda.Builtin.Word
open import Agda.Builtin.Float

instance
  IBootEq:Word64 : IBootEq Word64
  IBootEq._≟_ IBootEq:Word64 a b = primWord64ToNat a ≟ primWord64ToNat b

  IBootEq:Float : IBootEq Float
  IBootEq._≟_ IBootEq:Float  = primFloatEquality
