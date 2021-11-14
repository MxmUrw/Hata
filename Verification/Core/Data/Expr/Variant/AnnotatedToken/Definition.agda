
module Verification.Core.Data.Expr.Variant.AnnotatedToken.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FinR.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Algebra.AllOf.Pointed

-- open import Verification.Core.Data.Expr.Variant.AnnotatedList.Definition
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data

open import Verification.Core.Data.Substitution.Variant.Normal.Definition

data ATokenExprAnn : 𝒰₀ where
  varᵗ tokenᵗ : ATokenExprAnn

module _ (𝒹 : ATokenExprData) (Ann : ATokenExprAnn -> 𝐏𝐭𝐝₀) where
  data ATokenExprᵘ (X : 𝒰₀) : 𝒰₀ where
    var : ⟨ Ann varᵗ ⟩ -> Text -> ATokenExprᵘ X
    hole : X -> ATokenExprᵘ X
    token : ⟨ Ann tokenᵗ ⟩ -> TokenType 𝒹 -> ATokenExprᵘ X
    list : ∀{n} -> ConstDList (ATokenExprᵘ X) n -> ATokenExprᵘ X
    -- annotation : Text -> ATokenExprᵘ X -> ATokenExprᵘ X


module _ (𝒹 : ATokenExprData) (Ann) where
  macro ATokenExpr = #structureOn (ATokenExprᵘ 𝒹 Ann)




