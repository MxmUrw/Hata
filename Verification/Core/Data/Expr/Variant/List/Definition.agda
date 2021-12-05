
module Verification.Core.Data.Expr.Variant.List.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FinR.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
-- open import Verification.Core.Data.SourceCode.Variant.Tokenized.Definition

open import Verification.Core.Data.SourceCode.Variant.HaskellLike.Definition


data ListExprᵘ (X : 𝒰₀) : 𝒰₀ where
  var : Text -> ListExprᵘ X
  hole : X -> ListExprᵘ X
  list : List (ListExprᵘ X) -> ListExprᵘ X
  annotation : Text -> ListExprᵘ X -> ListExprᵘ X

macro ListExpr = #structureOn ListExprᵘ


module _ {X : 𝒰₀} where
  mutual
    parseHorizontal : Vec (ℕ +-𝒰 HaskellLikeSourceCode X) n -> Vec (List (ListExprᵘ X)) n
    parseHorizontal [] = []
    parseHorizontal (left x ∷ xs) = [] ∷ parseHorizontal xs
    parseHorizontal (just x ∷ xs) = makeListExprᵘs x ∷ parseHorizontal xs

    parseVertical : Vec (HaskellLikeSourceCode X) n -> Vec (List (ListExprᵘ X)) n
    parseVertical [] = []
    parseVertical (x ∷ xs) = makeListExprᵘs x ∷ parseVertical xs

    makeListExprᵘs : HsCode X -> List (ListExprᵘ X)
    makeListExprᵘs (hole x) = (hole x) ∷ []
    makeListExprᵘs (var x) = (var x) ∷ []
    makeListExprᵘs (newline x) = []
    makeListExprᵘs (horizontal x) = pure-List (list (join-List ((Vec→List (parseHorizontal x)))))
    makeListExprᵘs (vertical _ x) = join-List ((Vec→List (parseVertical x)))

    makeListExprᵘ : HsCode X -> (ListExprᵘ X)
    makeListExprᵘ x = list (makeListExprᵘs x)

module _ {X : 𝒰₀} {{_ : IShow X}} where
  instance
    IShow:ListExprᵘ : IShow (ListExprᵘ X)
    IShow:ListExprᵘ = record { show = f }
      where
        mutual
          fs : List (ListExprᵘ X) -> Text
          fs [] = ""
          fs (x ∷ xs) = f x <> " " <> fs xs

          f : ListExprᵘ X -> Text
          f (hole x) = show x
          f (var x) = show x
          f (list x) = "(" <> fs x <> ")"
          f (annotation t x) = "{" <> t <> "} " <> f x

module _ {X : 𝒰₀} where
  data ListExprᵘLoc : (γ : ListExprᵘ X) -> 𝒰₀ where
    hole : ∀{x : X} -> ListExprᵘLoc (hole x)
    list : ∀{xs : List (ListExprᵘ X)} -> (i : Fin-R (length xs))
         -> ListExprᵘLoc (lookup' xs i)
         -> ListExprᵘLoc (list xs)


  makeListExprᵘLoc : ∀{γ : HsCode X} -> HsLoc γ -> ListExprᵘLoc (makeListExprᵘ γ)
  makeListExprᵘLoc {hole x₁} hole = list zero hole
  makeListExprᵘLoc {horizontal x₁} (horizontal i x x₂) = {!!}
  makeListExprᵘLoc {vertical x₁ x₂} x = {!!}




