
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.StrictId where

open import Verification.Conventions.Proprelude

data StrId {a} {A : 𝒰 a} (x : A) : A → 𝒰 a where
  instance refl-StrId : StrId x x

