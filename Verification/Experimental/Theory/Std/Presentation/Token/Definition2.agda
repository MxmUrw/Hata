
module Verification.Experimental.Theory.Std.Presentation.Token.Definition2 where

{-# FOREIGN GHC import Hata.Runtime.Experimental.Theory.Std.Presentation.Token.Definition2 #-}
{-# FOREIGN GHC import Data.HashMap.Strict (HashMap) #-}


open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.Sum.Instance.Monad
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.List.Instance.Traversable
open import Verification.Experimental.Data.Substitution.Variant.Base.Definition


-----------------------------------------
-- basic trees

data Tree (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  node : A -> List (String ×~ Tree A B) -> Tree A B
  var  : B -> Tree A B
  hole : String -> Tree A B

{-# FOREIGN GHC type Tree' a b = Tree #-}
{-# COMPILE GHC Tree = data Tree' (Node | Var | Hole) #-}

-----------------------------------------
-- trees with correct number of arguments

module _ (A : 𝒰 𝑖) (l : A -> ℕ) where
  data VecTree1 : 𝒰 (𝑖) where
    node1 : (a : A) -> (Vec VecTree1 (l a)) -> VecTree1



record TokenTyping (Tok : 𝒰₀) : 𝒰₀ where
  field nextTokens : Tok -> ℕ
  field nextTokensBind : ∀(t : Tok) -> Vec ℕ (nextTokens t)
  field holeToken : Tok
  field variableToken : ℕ -> Tok


record TokenDefinition (Tok : 𝒰₀) : 𝒰₀ where
  field all : List Tok
  field name : Tok -> String

{-# COMPILE GHC TokenDefinition = data TokenDefinition (TokenDefinition) #-}


postulate
  parseTokens : ∀{A : 𝒰₀} -> TokenDefinition A -> String -> String +-𝒰 Tree A String

{-# COMPILE GHC parseTokens = \a -> parseTokens #-}

record FromString (A : 𝒰₀) : 𝒰₀ where
  field fromString : String -> String +-𝒰 A

open FromString {{...}} public




