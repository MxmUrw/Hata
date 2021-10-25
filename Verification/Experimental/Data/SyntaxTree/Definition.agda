
module Verification.Experimental.Data.SyntaxTree.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

record SyntaxTreeData : 𝒰₁ where
  field TokenType : 𝒰₀
  field TokenSize : TokenType -> ℕ

open SyntaxTreeData public




