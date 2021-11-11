
module Verification.Core.Data.Expr.Variant.Token.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FinR.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Data.Expr.Variant.List.Definition
open import Verification.Core.Data.Expr.Variant.Token.Data

open import Verification.Core.Data.Substitution.Variant.Normal.Definition


module _ (𝒹 : TokenExprData) where
  data TokenExprᵘ (X : 𝒰₀) : 𝒰₀ where
    var : Text -> TokenExprᵘ X
    hole : X -> TokenExprᵘ X
    token : TokenType 𝒹 -> TokenExprᵘ X
    list : ∀{n} -> ConstDList (TokenExprᵘ X) n -> TokenExprᵘ X
    annotation : Text -> TokenExprᵘ X -> TokenExprᵘ X


module _ (𝒹 : TokenExprData) where
  macro TokenExpr = #structureOn (TokenExprᵘ 𝒹)





