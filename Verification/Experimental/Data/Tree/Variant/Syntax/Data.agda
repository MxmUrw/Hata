
module Verification.Experimental.Data.Tree.Variant.Syntax.Data where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

record SyntaxTreeData : 𝒰₁ where
  field TokenType : 𝒰₀
  field tokenSize : TokenType -> ℕ
  field tokenBind : ∀(t : TokenType) -> Fin-R (tokenSize t) -> ℕ
  field tokenName : TokenType -> String
  field tokenList : List TokenType

open SyntaxTreeData public



