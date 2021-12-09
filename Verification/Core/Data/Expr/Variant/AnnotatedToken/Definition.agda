
module Verification.Core.Data.Expr.Variant.AnnotatedToken.Definition where

open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FinR.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Algebra.AllOf.Pointed

-- open import Verification.Core.Data.Expr.Variant.AnnotatedList.Definition
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data

open import Verification.Core.Data.Substitution.Variant.Normal.Definition

data ATokenExprAnnᵈ : 𝒰₀ where
  isvar istoken iscall : ATokenExprAnnᵈ

macro ATokenExprAnn = #structureOn (Maybe ATokenExprAnnᵈ)

module _ (𝒹 : ATokenExprData) (Ann : 𝐏𝐭𝐝₀) where
  data ATokenExprᵘ (X : 𝒰₀) : 𝒰₀ where
    var : ⟨ Ann ⟩ -> Text -> ATokenExprᵘ X
    hole : X -> ATokenExprᵘ X
    token : ⟨ Ann ⟩ -> TokenType 𝒹 -> ATokenExprᵘ X
    list : ∀{n} -> ⟨ Ann ⟩ -> ConstListᴰ (ATokenExprᵘ X) n -> ATokenExprᵘ X
    -- annotation : Text -> ATokenExprᵘ X -> ATokenExprᵘ X


module _ (𝒹 : ATokenExprData) (Ann) where
  macro ATokenExpr = #structureOn (ATokenExprᵘ 𝒹 Ann)




