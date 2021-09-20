
module Verification.Experimental.Theory.Std.Presentation.Token.Definition where

{-# FOREIGN GHC import Hata.Runtime.Experimental.Theory.Std.Presentation.Token.Definition #-}
{-# FOREIGN GHC import Data.HashMap.Strict (HashMap) #-}


open import Verification.Conventions
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition


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
  parseTokens : ∀{A : 𝒰₀} -> TokenDefinition A -> String -> String +-𝒰 Tree A String
  parseTwolines : ∀{A : 𝒰₀} -> TokenDefinition A -> String -> String +-𝒰 (Tree A String ×~ Tree A String)

{-# COMPILE GHC parseTokens = \a -> parseTokens #-}
{-# COMPILE GHC parseTwolines = \a -> parseTwolines #-}

record FromString (A : 𝒰₀) : 𝒰₀ where
  field fromString : String -> String +-𝒰 A

open FromString {{...}} public

--------------------------------------------------------------
-- Helpers

asFin : ∀{n} -> (m : ℕ) -> Maybe (Fin-R n)
asFin {zero} m = nothing
asFin {suc n} zero = just zero
asFin {suc n} (suc m) = map suc (asFin {n} m)

--------------------------------------------------------------
-- Finite containers

record isContainer (K : 𝒰 𝑖) (V : 𝒰 𝑗) (D : 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field emptyC : D
  field lookupC : K -> D -> Maybe V
  field addValue : K -> V -> D -> D

open isContainer {{...}} public

{-# FOREIGN GHC type IsContainer' a b c = IsContainer #-}
{-# COMPILE GHC isContainer = data IsContainer' (IsContainer) #-}

module _ (K : 𝒰 𝑖) (V : 𝒰 𝑗) (𝑘 : 𝔏) where
  Container = 𝒰 𝑘 :& isContainer K V


postulate
  StringHashMap : 𝒰₀ -> 𝒰₀
  instance
    isContainer:StringHashMap : ∀{V} -> isContainer String V (StringHashMap V)


{-# COMPILE GHC StringHashMap = type TextHashMap #-}
{-# COMPILE GHC isContainer:StringHashMap = \a -> isContainer_TextHashMap #-}



--------------------------------------------------------------
-- "unique" containers


module _ {K : 𝒰 𝑖} {D : 𝒰 𝑘} {{_ : isContainer K ℕ D}} where
  UniqueCon = ℕ ×-𝒰 D

  addUC : K -> UniqueCon -> (ℕ ×-𝒰 UniqueCon)
  addUC k (n , d) =
    case lookupC k d of
         (λ x → n , (suc n , addValue k n d))
         (λ v → v , (n , d))


--------------------------------------------------------------
-- algorithms


  module _ {A : 𝒰 𝑗} where

    mutual
      renameFreeVariables' : UniqueCon -> List (Tree A K) -> (UniqueCon) ×-𝒰 List (Tree A ℕ)
      renameFreeVariables' d [] = d , []
      renameFreeVariables' d (x ∷ xs) = let d' , x' = renameFreeVariables d x
                                            ds , xs = renameFreeVariables' d' xs
                                        in  ds , x' ∷ xs

      renameFreeVariables : UniqueCon -> Tree A K -> (UniqueCon) ×-𝒰 Tree A ℕ
      renameFreeVariables d (node x xs) = let d , r = renameFreeVariables' d xs in d , node x r
      renameFreeVariables d (var x) = let r , d = (addUC x d) in d , var r

    mutual
      finitizeFreeVariables' : (d : UniqueCon) -> List (Tree A ℕ) -> Maybe (List (Tree A (Fin-R (fst d))))
      finitizeFreeVariables' d [] = right []
      finitizeFreeVariables' d (x ∷ ts) with finitizeFreeVariables d x | finitizeFreeVariables' d ts
      ... | left x₁ | Y = left tt
      ... | just x₁ | left x₂ = left tt
      ... | just x | just ts = just (x ∷ ts)


      finitizeFreeVariables : (d : UniqueCon) -> (Tree A ℕ) -> Maybe (Tree A (Fin-R (fst d)))
      finitizeFreeVariables d (node x xs) with finitizeFreeVariables' d xs
      ... | left x₁ = left tt
      ... | just xs = right (node x xs)
      finitizeFreeVariables (n , d) (var x) with asFin {n} x
      ... | left x₁ = left tt
      ... | just y = right (var y)




