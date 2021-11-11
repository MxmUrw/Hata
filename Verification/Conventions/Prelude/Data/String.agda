

module Verification.Conventions.Prelude.Data.String where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.StrictId
open import Verification.Conventions.Prelude.Data.Bool

open import Agda.Builtin.Char

instance
  IBootMonoid:String : IBootMonoid String
  IBootMonoid.mempty IBootMonoid:String = ""
  IBootMonoid._<>_ IBootMonoid:String = primStringAppend

  IShow:String : IShow String
  IShow.show IShow:String s = s

  IBootEq:String : IBootEq String
  IBootEq._≟_ IBootEq:String = primStringEquality

  IBootEq:Char : IBootEq Char
  IBootEq._≟_ IBootEq:Char = primCharEquality

  isDiscrete:String : isDiscrete Text
  isDiscrete:String = record { _≟-Str_ = lem-1 }
    where
      lem-1 : (a b : Text) → Decision (StrId a b)
      lem-1 a b with a ≟ b
      ... | false = no λ x → bot
        where
          postulate bot : 𝟘-𝒰
      ... | true = yes eq
        where
          postulate eq : a ≣ b

