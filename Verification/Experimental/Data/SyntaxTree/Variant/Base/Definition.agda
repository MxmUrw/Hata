
module Verification.Experimental.Data.SyntaxTree.Variant.Base.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Data.SyntaxTree.Definition


data BaseSyntaxTreeᵘ (D : SyntaxTreeData) (A : 𝒰₀) : 𝒰₀ where
  hole : A -> BaseSyntaxTreeᵘ D A
  var : Text -> BaseSyntaxTreeᵘ D A
  node : (t : TokenType D) -> Vec (BaseSyntaxTreeᵘ D A) (TokenSize D t) -> BaseSyntaxTreeᵘ D A
  annotation : Text -> BaseSyntaxTreeᵘ D A -> BaseSyntaxTreeᵘ D A

module _ (D : SyntaxTreeData) where
  macro BaseSyntaxTree = #structureOn (BaseSyntaxTreeᵘ D)






