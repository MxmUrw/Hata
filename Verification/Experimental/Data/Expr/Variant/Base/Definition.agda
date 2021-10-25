
module Verification.Experimental.Data.Expr.Variant.Base.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

{-# FOREIGN GHC import Hata.Runtime.Experimental.Data.Expr.Variant.Base.Definition #-}

----------------------------------------------------------
-- definition of tokens for parsing

record hasElementNames (Tok : 𝒰₀) : 𝒰₀ where
  field all : List Tok
  field name : Tok -> Text

open hasElementNames {{...}} public

{-# COMPILE GHC hasElementNames = data HasElementNames (HasElementNames) #-}


----------------------------------------------------------
-- Haskell Version
-- the expressions which are parsed

data BaseExpr~ (A : 𝒰₀) (X : 𝒰₀) : 𝒰₀ where
  hole : X -> BaseExpr~ A X
  var : Text -> BaseExpr~ A X
  token : A -> BaseExpr~ A X
  list : List (BaseExpr~ A X) -> BaseExpr~ A X

{-# COMPILE GHC BaseExpr~ = data BaseExpr (Hole | Var | Token | List) #-}

postulate
  parseBaseExpr~ : ∀{A : 𝒰₀} -> (D : hasElementNames A) -> Text -> Text +-𝒰 BaseExpr~ A Text

{-# COMPILE GHC parseBaseExpr~ = \a -> parseBaseExpr #-}


----------------------------------------------------------
-- concisely parametrized version

record BaseExprData : 𝒰₁ where
  field TokenType : 𝒰₀
  field {{IShow:TokenType}} : IShow TokenType
  field {{hasElementNames:TokenType}} : hasElementNames TokenType

open BaseExprData public

data BaseExprᵘ (P : BaseExprData) (X : 𝒰₀) : 𝒰₀ where
  hole : X -> BaseExprᵘ P X
  var : Text -> BaseExprᵘ P X
  token : TokenType P -> BaseExprᵘ P X
  list : List (BaseExprᵘ P X) -> BaseExprᵘ P X
  annotation : Text -> BaseExprᵘ P X -> BaseExprᵘ P X


module _ (P : BaseExprData) where
  macro BaseExpr = #structureOn (BaseExprᵘ P)


module _ {P : BaseExprData} where
  instance
    IShow:BaseExpr : ∀{X} -> {{_ : IShow X}} -> IShow (BaseExprᵘ P X)
    IShow:BaseExpr {X} = record { show = f }
      where
        mutual
          fs : List (BaseExpr P X) -> Text
          fs [] = ""
          fs (x ∷ xs) = f x <> " " <> fs xs

          f : BaseExpr P X -> Text
          f (var x) = show x
          f (token x) = name x
          f (list x) = "(" <> fs x <> ")"
          f (hole x) = "?{" <> show x <> "}"
          f (annotation t rest) = "[" <> t <> "](" <> f rest <> ")"

instance
  IShow:⊤-𝒰 : IShow (⊤-𝒰 {𝑖})
  IShow:⊤-𝒰 = record { show = const "()" }

--------------
-- Haskell to native version

instance
  hasInclusion:BaseExpr~,BaseExpr : ∀{P X} -> hasInclusion (BaseExpr~ (TokenType P) X) (BaseExpr P X)
  hasInclusion:BaseExpr~,BaseExpr {P} {X} = inclusion ι'
    where
      mutual
        ι's : List (BaseExpr~ (TokenType P) X) -> List (BaseExpr P X)
        ι's [] = []
        ι's (x ∷ xs) = ι' x ∷ ι's xs

        ι' : (BaseExpr~ (TokenType P) X) -> (BaseExpr P X)
        ι' (hole x) = hole x
        ι' (var x) = var x
        ι' (token x) = token x
        ι' (list x) = list (ι's x)

parseBaseExpr : ∀{P : BaseExprData} -> Text -> Text + BaseExpr P Text
parseBaseExpr = mapRight ι ∘ parseBaseExpr~ it


