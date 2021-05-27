
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Monad.Instance.FreeMonoid where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Monad.Definition
--- open import Verification.Core.Algebra.Monoid

--------------------------------------------------------------------
-- Free Monoid Monad (aka List Monad)

-- map-List : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (f : A -> B) -> (List A -> List B)
-- map-List f [] = []
-- map-List f (x ∷ xs) = f x ∷ map-List f xs

join-List : ∀{A : 𝒰 𝑖} -> (List (List A)) -> List A
join-List xs = {!!}

instance
  IFunctor:List : IFunctor (Category:𝒰 𝑖) (Category:𝒰 𝑖) List
  IFunctor.map IFunctor:List = map-List
  IFunctor.functoriality-id IFunctor:List = {!!}
  IFunctor.functoriality-◆ IFunctor:List = {!!}
  IFunctor.functoriality-≣ IFunctor:List = {!!}

instance
  IMonad:List : IMonad {𝒞 = (Category:𝒰 𝑖)} (′ List ′)
  -- IMonad.FunctorInstance IMonad:List = IFunctor:List
  IMonad.return IMonad:List a = a ∷ []
  IMonad.INatural:return IMonad:List = {!!}
  IMonad.join IMonad:List = join-List
  IMonad.INatural:join IMonad:List = {!!}
  IMonad.unit-l-join IMonad:List = {!!}
  IMonad.unit-r-join IMonad:List = {!!}
  IMonad.assoc-join IMonad:List = {!!}


