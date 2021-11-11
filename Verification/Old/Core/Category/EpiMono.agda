
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.EpiMono where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory 𝒞 𝑗}} where
  record IMono {X Y : 𝒞} (f : Hom X Y) : 𝒰 (𝑖 ､ 𝑗) where
    field isMono : ∀{W} -> (g h : Hom W X) -> (g ◆ f ≣ h ◆ f) -> g ≣ h

  open IMono {{...}} public

  record Mono (X Y : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field ⟨_⟩ : Hom X Y
          {{Impl}} : IMono ⟨_⟩




