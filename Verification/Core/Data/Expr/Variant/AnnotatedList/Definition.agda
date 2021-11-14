
module Verification.Core.Data.Expr.Variant.AnnotatedList.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FinR.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Universe.Everything
-- open import Verification.Core.Data.SourceCode.Variant.Tokenized.Definition

open import Verification.Core.Data.SourceCode.Variant.HaskellLike.Definition

open import Verification.Core.Algebra.Pointed.Definition


data AListExprAnn : 𝒰₀ where
  varᵗ : AListExprAnn


data AListExprᵘ (A : AListExprAnn -> 𝐏𝐭𝐝₀) (X : 𝒰₀) : 𝒰₀ where
  var : ⟨ A varᵗ ⟩ -> Text -> AListExprᵘ A X
  hole : X -> AListExprᵘ A X
  list : List (AListExprᵘ A X) -> AListExprᵘ A X
  -- annotation : Text -> AListExprᵘ A X -> AListExprᵘ A X

module _ (A : AListExprAnn -> 𝐏𝐭𝐝₀) where
  macro AListExpr = #structureOn (AListExprᵘ A)


module _ {A : AListExprAnn -> 𝐏𝐭𝐝₀} {X : 𝒰₀} where
  mutual
    parseHorizontal : Vec (ℕ +-𝒰 HaskellLikeSourceCode X) n -> Vec (List (AListExprᵘ A X)) n
    parseHorizontal [] = []
    parseHorizontal (left x ∷ xs) = [] ∷ parseHorizontal xs
    parseHorizontal (just x ∷ xs) = makeAListExprᵘs x ∷ parseHorizontal xs

    parseVertical : Vec (HaskellLikeSourceCode X) n -> Vec (List (AListExprᵘ A X)) n
    parseVertical [] = []
    parseVertical (x ∷ xs) = makeAListExprᵘs x ∷ parseVertical xs

    makeAListExprᵘs : HsCode X -> List (AListExprᵘ A X)
    makeAListExprᵘs (hole x) = (hole x) ∷ []
    makeAListExprᵘs (var x) = (var (pt {{of A varᵗ}}) x) ∷ []
    makeAListExprᵘs (newline x) = []
    makeAListExprᵘs (horizontal x) = pure-List (list (join-List ((Vec→List (parseHorizontal x)))))
    makeAListExprᵘs (vertical _ x) = join-List ((Vec→List (parseVertical x)))

    makeAListExprᵘ : HsCode X -> (AListExprᵘ A X)
    makeAListExprᵘ x = list (makeAListExprᵘs x)

module _ {A : AListExprAnn -> 𝐏𝐭𝐝₀} {X : 𝒰₀} {{_ : IShow X}} {{_ : ∀{a} -> IShow (⟨ A a ⟩)}} where
  instance
    IShow:AListExprᵘ : IShow (AListExprᵘ A X)
    IShow:AListExprᵘ = record { show = f }
      where
        mutual
          fs : List (AListExprᵘ A X) -> Text
          fs [] = ""
          fs (x ∷ xs) = f x <> " " <> fs xs

          f : AListExprᵘ A X -> Text
          f (hole x) = show x
          f (var ann x) = "{" <> show ann <> "} " <> show x
          f (list x) = "(" <> fs x <> ")"


          -- f (annotation t x) = "{" <> t <> "} " <> f x


{-
module _ {A} {X : 𝒰₀} where
  data AListExprᵘLoc : (γ : AListExprᵘ A X) -> 𝒰₀ where
    hole : ∀{x : X} -> AListExprᵘLoc (hole x)
    list : ∀{xs : List (AListExprᵘ A X)} -> (i : Fin-R (length xs))
         -> AListExprᵘLoc (lookup' xs i)
         -> AListExprᵘLoc (list xs)


  makeAListExprᵘLoc : ∀{γ : HsCode X} -> HsLoc γ -> AListExprᵘLoc (makeAListExprᵘ γ)
  makeAListExprᵘLoc {hole x₁} hole = list zero hole
  makeAListExprᵘLoc {horizontal x₁} (horizontal i x x₂) = {!!}
  makeAListExprᵘLoc {vertical x₁ x₂} x = {!!}

-}

