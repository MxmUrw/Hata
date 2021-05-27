
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Classes.Computational where

open import Verification.Conventions.Proprelude

record IShow (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field show : A -> String
open IShow {{...}} public

record IBootMonoid (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field mempty : A
        _<>_ : A -> A -> A
  infixl 30 _<>_
open IBootMonoid {{...}} public

record IBootEq (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field _≟_ : A -> A -> Bool
open IBootEq {{...}} public

