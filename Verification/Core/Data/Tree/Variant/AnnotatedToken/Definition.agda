
module Verification.Core.Data.Tree.Variant.AnnotatedToken.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Algebra.AllOf.Pointed
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
-- open import Verification.Core.Data.Nat.Free
-- open import Verification.Core.Data.Nat.Definition
-- open import Verification.Core.Data.AllOf.Sum
-- open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

open import Verification.Core.Data.Tree.Variant.AnnotatedToken.Data
-- open import Verification.Core.Data.Substitution.Variant.Normal.Definition

module _ (𝒹 : ATokenTreeData) where
  data ATokenTreeAnnᵈ  : 𝒰₀ where
    isvar : ATokenTreeAnnᵈ
    istoken : ATokenTreeAnnᵈ
    iserror : Text -> ATokenTreeAnnᵈ

  macro ATokenTreeAnn = #structureOn (Maybe ATokenTreeAnnᵈ)

module _ {𝒹 : ATokenTreeData} where
  instance
    IShow:ATokenTreeAnnᵈ : IShow (ATokenTreeAnnᵈ 𝒹)
    IShow:ATokenTreeAnnᵈ = record { show = lem-1 }
      where
        lem-1 : ATokenTreeAnnᵈ 𝒹 → Text
        lem-1 isvar = ""
        lem-1 istoken = ""
        lem-1 (iserror x) = "Error: " <> x


module _ (𝒹 : ATokenTreeData) (Ann : 𝐏𝐭𝐝₀) where
  data ATokenTreeᵘ (A : 𝒰₀) : 𝒰₀ where
    hole : A -> ATokenTreeᵘ A
    var : ⟨ Ann ⟩ -> Text -> ATokenTreeᵘ A
    node : ⟨ Ann ⟩ -> (t : TokenType 𝒹) -> ConstListᴰ (ATokenTreeᵘ A) (tokenSize 𝒹 t) -> ATokenTreeᵘ A
    -- annotation : Text -> ATokenTreeᵘ A -> ATokenTreeᵘ A

  macro ATokenTree = #structureOn (ATokenTreeᵘ)




-- module _ (𝒹 : ATokenTreeData) where
--   data ATokenTree (X : 𝒰₀) : 𝒰₀ where
--     hole : X -> ATokenTree X
--     var : Text -> ATokenTree X
--     token : (t : TokenType 𝒹) -> Vec (ATokenTree X) (tokenSize 𝒹 t) -> ATokenTree X


--   open import Verification.Core.Data.Expr.Variant.List.Definition

--   ListExpr→ATokenTree : ∀{X} -> ListExpr X -> ATokenTree (ListExpr X)
--   ListExpr→ATokenTree (var x) = var x
--   ListExpr→ATokenTree (hole x) = hole (hole x)
--   ListExpr→ATokenTree (list []) = hole (list [])
--   ListExpr→ATokenTree (list (x ∷ x₁)) = {!!}




