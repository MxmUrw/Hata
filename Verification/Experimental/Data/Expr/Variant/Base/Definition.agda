
module Verification.Experimental.Data.Expr.Variant.Base.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)


data BaseExpr : 𝒰₀ where
  token : String -> BaseExpr
  list : List BaseExpr -> BaseExpr






