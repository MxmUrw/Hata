
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Monad.Instance.FreeMonoidModule where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Monad.Definition
open import Verification.Old.Core.Algebra.Basic.Monoid

--------------------------------------------------------------------
-- Free Monoid Module Monad (aka Writer Monad)


instance
  IFunctor:×-𝒰 : {a : 𝒰 𝑖} -> IFunctor (category (𝒰 𝑖)) (category (𝒰 𝑖)) (a ×-𝒰_)
  IFunctor.map (IFunctor:×-𝒰 {a = a}) f (x , y) = (x , f y)
  IFunctor.functoriality-id IFunctor:×-𝒰 = {!!}
  IFunctor.functoriality-◆ IFunctor:×-𝒰 = {!!}
  IFunctor.functoriality-≣ IFunctor:×-𝒰 = {!!}

-- test : {A B C : 𝒰₀} -> (f : A -> B) -> (C ×-𝒰 A) -> (C ×-𝒰 B)
-- test f = map f



instance
  IMonad:× : ∀{M : 𝒰 𝑖} -> {{_ : IMonoid M}} -> IMonad (′ (M ×-𝒰_) ′)
  -- IMonad.FunctorInstance IMonad:× = IFunctor:×-𝒰
  IMonad.return IMonad:× a = 𝟷 , a
  IMonad.INatural:return IMonad:× = {!!}
  IMonad.join IMonad:× (m , (n , a)) = (n ⋅ m , a)
  IMonad.INatural:join IMonad:× = {!!}
  IMonad.unit-l-join IMonad:× = {!!}
  IMonad.unit-r-join IMonad:× = {!!}
  IMonad.assoc-join IMonad:× = {!!}

tell : ∀{M : 𝒰 𝑖} -> {{_ : IMonoid M}} -> M -> (M ×-𝒰 𝟙-𝒰)
tell m = m , tt
