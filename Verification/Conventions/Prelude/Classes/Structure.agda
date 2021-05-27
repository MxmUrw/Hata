
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Classes.Structure where

open import Verification.Conventions.Proprelude


-- infixl 10 ⌘_
record Structure {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  constructor ′_′
  field ⟨_⟩ : A
        {{of_}} : P ⟨_⟩
        -- of_ : P ⟨_⟩

  infixr 2 of_

open Structure public

