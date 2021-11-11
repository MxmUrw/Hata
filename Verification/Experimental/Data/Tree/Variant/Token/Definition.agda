
module Verification.Experimental.Data.Tree.Variant.Token.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Data.Tree.Variant.Token.Data


data TokenTreeᵘ (𝒹 : TokenTreeData) (A : 𝒰₀) : 𝒰₀ where
  hole : A -> TokenTreeᵘ 𝒹 A
  var : Text -> TokenTreeᵘ 𝒹 A
  node : (t : TokenType 𝒹) -> Vec (TokenTreeᵘ 𝒹 A) (tokenSize 𝒹 t) -> TokenTreeᵘ 𝒹 A
  annotation : Text -> TokenTreeᵘ 𝒹 A -> TokenTreeᵘ 𝒹 A

module _ (𝒹 : TokenTreeData) where
  macro TokenTree = #structureOn (TokenTreeᵘ 𝒹)




-- module _ (𝒹 : TokenTreeData) where
--   data TokenTree (X : 𝒰₀) : 𝒰₀ where
--     hole : X -> TokenTree X
--     var : Text -> TokenTree X
--     token : (t : TokenType 𝒹) -> Vec (TokenTree X) (tokenSize 𝒹 t) -> TokenTree X


--   open import Verification.Experimental.Data.Expr.Variant.List.Definition

--   ListExpr→TokenTree : ∀{X} -> ListExpr X -> TokenTree (ListExpr X)
--   ListExpr→TokenTree (var x) = var x
--   ListExpr→TokenTree (hole x) = hole (hole x)
--   ListExpr→TokenTree (list []) = hole (list [])
--   ListExpr→TokenTree (list (x ∷ x₁)) = {!!}





