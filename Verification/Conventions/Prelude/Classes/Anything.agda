
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Classes.Anything where

open import Verification.Conventions.Proprelude

record IAnything {A : 𝒰 𝑖} (a : A) : 𝒰₀ where
instance
  IAnything:A : ∀{A : 𝒰 𝑖} {a : A} -> IAnything a
  IAnything:A = record {}
