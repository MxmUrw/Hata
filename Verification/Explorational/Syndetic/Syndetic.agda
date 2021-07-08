
module Verification.Experimental.Category.Syndetic where

open import Verification.Conventions hiding (Square ; extend)
open import Verification.Core.Category.Definition



module _ (𝒞 : Category 𝑖) where

  -- Square : (a b c d : ⟨ 𝒞 ⟩) -> 𝒰 𝑖
  -- Square a b c d = {!!}

  Vee : (a b : ⟨ 𝒞 ⟩) -> 𝒰 _
  Vee a b = ∑ λ x -> (a ⟶ x ×-𝒰 b ⟶ x)

  record Syndetic (𝑗 : 𝔏 ^ 2) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
    field Term : ∀{a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) ->  𝒰 (𝑗 ⌄ 0) -- but we only need f : a ⟶ b, g : a' ⟶ b
          Filler : {a b c d : ⟨ 𝒞 ⟩} -> (a ⟶ b) -> (c ⟶ d) -> 𝒰 (𝑗 ⌄ 1)
          extend : ∀{a b c d} -> {f : a ⟶ b} -> {g : c ⟶ d} -> Filler f g -> Vee b d

    extend-o : ∀{a b c d : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> {g : c ⟶ d} -> (ϕ : Filler f g) -> ⟨ 𝒞 ⟩
    extend-o ϕ = extend ϕ .fst

    extend-l : ∀{a b c d : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> {g : c ⟶ d} -> (ϕ : Filler f g) -> b ⟶ extend-o ϕ
    extend-l ϕ = extend ϕ .snd .fst

    extend-r : ∀{a b c d : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> {g : c ⟶ d} -> (ϕ : Filler f g) -> d ⟶ extend-o ϕ
    extend-r ϕ = extend ϕ .snd .snd

    -- TODO: Fill on both sides?
    -- field compose : ∀{a b c d : ⟨ 𝒞 ⟩} -> {f f' : a ⟶ b} -> {g g' : c ⟶ d} -> Term f f' -> (ϕ : Filler f' g) -> Term g g' -> Term (f ◆ extend-l ϕ) (g ◆ extend-r ϕ)




