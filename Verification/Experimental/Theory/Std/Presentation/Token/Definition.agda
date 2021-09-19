
module Verification.Experimental.Theory.Std.Presentation.Token.Definition where

{-# FOREIGN GHC import Hata.Runtime.Experimental.Theory.Std.Presentation.Token.Definition #-}

open import Verification.Conventions


record TokenDefinition (Tok : 𝒰₀) : 𝒰₀ where
  field all : List Tok
  field name : Tok -> String

{-# COMPILE GHC TokenDefinition = data TokenDefinition (TokenDefinition) #-}

data Tree (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  node : A -> List (Tree A B) -> Tree A B
  var  : B -> Tree A B

{-# FOREIGN GHC type Tree' a b = Tree #-}
{-# COMPILE GHC Tree = data Tree' (Node | Var) #-}

postulate
  parseTokens : ∀{A : 𝒰₀} -> TokenDefinition A -> String -> Tree A String


record FromString (A : 𝒰₀) : 𝒰₀ where
  field fromString : String -> String +-𝒰 A

open FromString {{...}} public



