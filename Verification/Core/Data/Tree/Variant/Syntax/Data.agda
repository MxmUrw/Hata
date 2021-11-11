
module Verification.Core.Data.Tree.Variant.Syntax.Data where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Universe.Everything


record SyntaxTreeData : 𝒰₁ where
  field TokenType : 𝒰₀
  field tokenSize : TokenType -> List (♮ℕ)
  -- field tokenBind : ∀(t : TokenType) -> Fin-R (tokenSize t) -> ℕ
  field tokenName : TokenType -> String
  field tokenList : List TokenType

open SyntaxTreeData public



