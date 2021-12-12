
module Verification.Core.Data.Expr.Variant.Token.Data where

open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

record TokenExprData : 𝒰₁ where
  field TokenType : 𝒰₀
  field tokenName : TokenType -> String
  field tokenList : List TokenType

open TokenExprData public


