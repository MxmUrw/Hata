
module Verification.Core.Theory.Std.Presentation.Token.Definition2 where

{-# FOREIGN GHC import Hata.Runtime.Core.Theory.Std.Presentation.Token.Definition2 #-}
{-# FOREIGN GHC import Data.HashMap.Strict (HashMap) #-}


open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Sum.Instance.Functor
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Sum.Instance.Monad
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Unary.Instance.Traversable
open import Verification.Core.Data.Substitution.Variant.Base.Definition


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




