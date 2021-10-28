
module Verification.Experimental.Data.SourceCode.Variant.Tokenized.HaskellLike.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.SourceCode.Variant.Tokenized.Definition

{-# FOREIGN GHC import Hata.Runtime.Experimental.Data.SourceCode.Variant.Tokenized.HaskellLike.Definition #-}
{-# FOREIGN GHC import Hata.Runtime.Experimental.Data.SourceCode.Variant.Tokenized.Definition #-}


----------------------------------------------------------
-- Haskell version

data HaskellLikeTokenizedSourceCode~ (T : 𝒰₀) (X : 𝒰₀) : 𝒰₀ where
  var : String -> HaskellLikeTokenizedSourceCode~ T X
  hole : X -> HaskellLikeTokenizedSourceCode~ T X
  token : T -> HaskellLikeTokenizedSourceCode~ T X
  horizontal : List (ℕ + HaskellLikeTokenizedSourceCode~ T X) -> HaskellLikeTokenizedSourceCode~ T X
  vertical  : ℕ -> List (HaskellLikeTokenizedSourceCode~ T X) -> HaskellLikeTokenizedSourceCode~ T X

{-# COMPILE GHC HaskellLikeTokenizedSourceCode~ = data HaskellLikeTokenizedSourceCode (Var | Hole | Token | Horizontal | Vertical) #-}

postulate
  parseHaskellLikeTokenizedSourceCode~ : ∀{A : 𝒰₀} -> (D : hasElementNames A) -> Text -> Text +-𝒰 HaskellLikeTokenizedSourceCode~ A Text

{-# COMPILE GHC parseHaskellLikeTokenizedSourceCode~ = \a -> parseHaskellLikeTokenizedSourceCode #-}


----------------------------------------------------------
-- Native version

module _ (d : TokenizedSourceCodeData) where
  data HaskellLikeTokenizedSourceCode (X : 𝒰₀) : 𝒰₀ where
    var : Text -> HaskellLikeTokenizedSourceCode X
    hole : X -> HaskellLikeTokenizedSourceCode X
    token : TokenType d -> HaskellLikeTokenizedSourceCode X
    horizontal : List (ℕ + HaskellLikeTokenizedSourceCode X) -> HaskellLikeTokenizedSourceCode X
    vertical  : ℕ -> List (HaskellLikeTokenizedSourceCode X) -> HaskellLikeTokenizedSourceCode X


module _ {d : TokenizedSourceCodeData} where
  instance
    IShow:HaskellLikeTokenizedSourceCode : ∀{X} -> {{_ : IShow X}} -> IShow (HaskellLikeTokenizedSourceCode d X)
    IShow:HaskellLikeTokenizedSourceCode {X} = record { show = f }
      where
        mutual
          space : ℕ -> Text
          space zero = ""
          space (suc n) = " " <> space n

          verts : List (ℕ + HaskellLikeTokenizedSourceCode d X) -> Text
          verts [] = ""
          verts (left n ∷ xs) = "\n" <> space n <> verts xs
          verts (just x ∷ xs) = f x <> " " <> verts xs

          horizs : ℕ -> List (HaskellLikeTokenizedSourceCode d X) -> Text
          horizs n [] = ""
          horizs n (x ∷ xs) = "\n" <> space n <> f x <> horizs n xs

          f : HaskellLikeTokenizedSourceCode d X → Text
          f (var x) = x
          f (hole x) = show x
          f (token x) = show x
          f (horizontal x) = "(" <> verts x <> ")"
          f (vertical n xs) = "where" <> horizs n xs


-------------------------
-- going from haskell to native


instance
  hasInclusion:HaskellLikeTokenizedSourceCode~,HaskellLikeTokenizedSourceCode : ∀{P X} -> hasInclusion (HaskellLikeTokenizedSourceCode~ (TokenType P) X) (HaskellLikeTokenizedSourceCode P X)
  hasInclusion:HaskellLikeTokenizedSourceCode~,HaskellLikeTokenizedSourceCode {P} {X} = inclusion f
    where
      mutual
        fs : List (ℕ + HaskellLikeTokenizedSourceCode~ (TokenType P) X) → List (ℕ + HaskellLikeTokenizedSourceCode P X)
        fs [] = []
        fs (left x ∷ xs) = left x ∷ fs xs
        fs (right x ∷ xs) = right (f x) ∷ fs xs

        gs : List (HaskellLikeTokenizedSourceCode~ (TokenType P) X) → List (HaskellLikeTokenizedSourceCode P X)
        gs [] = []
        gs (x ∷ xs) = f x ∷ gs xs

        f : HaskellLikeTokenizedSourceCode~ (TokenType P) X → HaskellLikeTokenizedSourceCode P X
        f (var x) = var x
        f (hole x) = hole x
        f (token x) = token x
        f (horizontal x) = horizontal (fs x)
        f (vertical n xs) = vertical n (gs xs)


parseHaskellLikeTokenizedSourceCode : ∀{P : TokenizedSourceCodeData} -> Text -> Text + HaskellLikeTokenizedSourceCode P Text
parseHaskellLikeTokenizedSourceCode = mapRight ι ∘ parseHaskellLikeTokenizedSourceCode~ it










