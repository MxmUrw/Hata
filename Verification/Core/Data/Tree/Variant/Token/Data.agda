
module Verification.Core.Data.Tree.Variant.Token.Data where

open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

record TokenTreeData : 𝒰₁ where
  field TokenType : 𝒰₀
  field tokenSize : TokenType -> ♮ℕ
  field tokenName : TokenType -> String
  field tokenList : List TokenType

open TokenTreeData public




