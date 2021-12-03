
module Verification.Core.Theory.Std.Presentation.Token.Definition where

{-

{-# FOREIGN GHC import Hata.Runtime.Core.Theory.Std.Presentation.Token.Definition #-}
{-# FOREIGN GHC import Data.HashMap.Strict (HashMap) #-}


open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.FreeMonoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Sum.Instance.Functor
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Sum.Instance.Monad
open import Verification.Core.Data.List.Variant.Base.Instance.Traversable
open import Verification.Core.Data.Substitution.Variant.Base.Definition


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
-- paths

module _ {A : 𝒰 𝑖} where
  length : List A -> ℕ
  length [] = 0
  length (x ∷ as) = suc (length as)

  lookup' : ∀(as : List A) -> Fin-R (length as) -> A
  lookup' (x ∷ as) zero = x
  lookup' (x ∷ as) (suc i) = lookup' as i

lookup : ∀ {n} {A : 𝒰 ℓ} → Fin-R n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

toVec : {A : 𝒰 ℓ} → (as : List A) -> Vec A (length as)
toVec [] = []
toVec (x ∷ as) = x ∷ toVec as

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

--------------------------------------------------------------
-- helper


case-Dec_of : ∀{A : 𝒰 𝑖} {C : 𝒰 𝑘} (a : Decision A) -> ((¬ A) -> C) -> (A -> C) -> C
case-Dec no x of f g = f x
case-Dec yes x of f g = g x

--------------------------------------------------------------
-- non computing lists and vectors

人Vec : (A : 𝒰 𝑖) -> (n : 人List (⊤-𝒰 {𝑖})) -> 𝒰 _
人Vec A n = CtxHom (λ x x₁ → A) n ◌

人ℕ' : ∀ 𝑖 -> 𝒰 _
人ℕ' 𝑖 = 人List (⊤-𝒰 {𝑖})

{-
module _ {R : 人List (⊤-𝒰 {𝑖}) -> ⊤-𝒰 {𝑖} -> 𝒰 𝑖} where
  asList : ∀{a b} -> CtxHom R a b -> 人List (R b tt)
  asList ◌-⧜ = ◌-⧜
  asList (incl {tt} x) = incl x
  asList (f ⋆-⧜ g) = asList f ⋆ asList g

  atList : ∀{a b} -> CtxHom R a b -> (i : [ a ]ᶠ) -> (R b tt)
  atList f (tt , p) = destruct-CtxHom f tt p

  -- atList (incl x) (tt , incl) = x
  -- atList (f ⋆-⧜ g) (a , right-∍ i) = atList g (_ , i)
  -- atList (f ⋆-⧜ g) (a , left-∍ i) = atList f (_ , i)

  atasList : ∀{a b} -> (σ : CtxHom R a b) -> (i : [ a ]ᶠ) -> asList σ ∍ atList σ i
  atasList (incl x) (tt , incl) = incl
  atasList (f ⋆-⧜ g) (tt , left-∍ i) = left-∍ (atasList f (_ , i))
  atasList (f ⋆-⧜ g) (tt , right-∍ i) = right-∍ (atasList g (_ , i))

  atasList' : ∀{a b} -> (σ : CtxHom R a b) -> (i : [ a ]ᶠ) -> ∀{x} -> atList σ i ≣ x -> asList σ ∍ x
  atasList' σ i refl-≣ = atasList σ i

-- module _ {A : 𝒰 𝑖} {R : 人List A -> A -> 𝒰 𝑖} where
--   fromIndexed : {as bs : 人List A} -> (∀{a} -> (as ∍ a) -> R bs a) -> CtxHom R as bs
--   fromIndexed {incl x} {bs} F = incl (F (incl))
--   fromIndexed {as1 ⋆-Free-𝐌𝐨𝐧 as2} {bs} F = (fromIndexed (λ x -> F (left-∍ x))) ⋆-⧜ ((fromIndexed (λ x -> F (right-∍ x))))
--   fromIndexed {◌-Free-𝐌𝐨𝐧} {bs} F = ◌-⧜
-}

module _ {R : ⊤-𝒰 {𝑖} -> 𝒰 𝑖} where
  asList : ∀{a} -> D人List R a -> 人List (R tt)
  asList ◌-⧜ = ◌-⧜
  asList (incl {tt} x) = incl x
  asList (f ⋆-⧜ g) = asList f ⋆ asList g

  atList : ∀{a} -> D人List R a -> (i : [ a ]ᶠ) -> (R tt)
  atList f (tt , p) = destruct-CtxHom f tt p

  atasList : ∀{a} -> (σ : D人List R a) -> (i : [ a ]ᶠ) -> asList σ ∍ atList σ i
  atasList (incl x) (tt , incl) = incl
  atasList (f ⋆-⧜ g) (tt , left-∍ i) = left-∍ (atasList f (_ , i))
  atasList (f ⋆-⧜ g) (tt , right-∍ i) = right-∍ (atasList g (_ , i))

  atasList' : ∀{a} -> (σ : D人List R a) -> (i : [ a ]ᶠ) -> ∀{x} -> atList σ i ≣ x -> asList σ ∍ x
  atasList' σ i refl-≣ = atasList σ i


--------------------------------------------------------------
-- Well branching trees

module _ (A : 𝒰 𝑖) (B : 𝒰 𝑗) (l : A -> 人ℕ' (𝑖 ､ 𝑗)) where
  data VecTree : 𝒰 (𝑖 ､ 𝑗) where
    node : (a : A) -> ([ l a ]ᶠ -> VecTree) -> VecTree
    -- node : (a : A) -> (人Vec VecTree (l a)) -> VecTree
    var  : B -> VecTree

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {l : A -> 人ℕ' (𝑖 ､ 𝑗)} where
  data TreeStep : (t s : VecTree A B l) -> 𝒰 (𝑖 ､ 𝑗) where
    -- incl : ∀{a : A} -> (ts : ([ l a ]ᶠ -> (VecTree A B l))) (s : VecTree A B l) -> (i : [ l a ]ᶠ)
    --        -> (ts i) ≣ s
    --        -> TreeStep (node a ts) s

    incl : ∀{a : A} -> (ts : ([ l a ]ᶠ -> (VecTree A B l))) -> (i : [ l a ]ᶠ)
           -> TreeStep (node a ts) (ts i)

    -- incl : ∀{a : A} -> (ts : (人Vec (VecTree A B l) (l a))) -> (i : [ l a ]ᶠ)
    --        -> TreeStep (node a ts) (atList ts i)

  data TreePath : (t s : VecTree A B l) -> 𝒰 (𝑖 ､ 𝑗) where
    [] : ∀{t : VecTree A B l} -> TreePath t t
    step : ∀{r s t : (VecTree A B l)} -> TreePath r s -> TreeStep s t -> TreePath r t

  {-# TERMINATING #-}
  makeVecTree : Tree A B -> Maybe (VecTree A B l)
  makeVecTree (node x xs) = {!!} -- do
  --   xs' <- mapM makeVecTree xs
  --   case-Dec length xs' ≟-Str l x of
  --                (λ _ -> left tt)
  --                (λ p → right (node x (transport-Str (cong-Str (λ ξ -> Vec _ ξ) p) (toVec xs'))))
  makeVecTree (var x) = right (var x)

{-
{-
-}
-}

-}
