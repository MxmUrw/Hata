
module Verification.Core.Data.Expr.Definition where

open import Verification.Conventions hiding (β)

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Category.Std.Category.Subcategory.Full


data Exprα΅ (B : π° π) (A : ππ’π§ππ± (β€-π° {π})) : π° π where
  val : B -> Exprα΅ B A
  var : β{a} -> β¨ A β© β a -> Exprα΅ B A
  statements : List (Exprα΅ B A) -> Exprα΅ B A


{-

-- rel monad

data Exprα΅ (B : π° π) (A : ππ’π§ππ± (β€-π° {π})) : π° π where
  val : B -> Exprα΅ B A
  var : β{a} -> β¨ A β© β a -> Exprα΅ B A
  statements : List (Exprα΅ B A) -> Exprα΅ B A

module _ (B : π° π) where
  Expr : ππ’π§ππ± β€-π° -> ππ± (β€-π° {π}) (ππ§π’π― π)
  Expr A = indexed (Ξ» i -> Exprα΅ B A)


-}


{-
-- product theory

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module

module _ {A : π° π} (a b : A) where
  data πListβ : List A -> A -> π° π where
    []α΅ : πListβ [] a
    β·α΅ : πListβ (b β· a β· []) a



module _ (B : π° π) where
  data πExprβ : π° π where
    εα΅ ε¨α΅ : πExprβ

  data πExprβ : List πExprβ β πExprβ β π° π where
    val : B -> πExprβ [] ε¨α΅
    list : β{a b} -> πListβ εα΅ ε¨α΅ a b -> πExprβ a b
    statements : πExprβ (εα΅ β· []) ε¨α΅



  πExpr : ProductTheory π
  Sort πExpr = πExprβ
  isDiscrete:Sort πExpr = {!!}
  isSet-Str:Sort πExpr = {!!}
  Con πExpr = πExprβ
  isDiscrete:Con πExpr = {!!}


-}



