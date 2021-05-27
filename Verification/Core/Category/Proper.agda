
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Proper where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Homotopy.Level

module _ (𝒞 : Category 𝑖) where
  private
    X = ⟨ 𝒞 ⟩
  record I1Category : 𝒰 (𝑖) where
    field {{ISet:Hom}} : ∀{a b : X} -> ISet (Hom a b)
          ≣→≡ : ∀{a b : X} -> ∀{f g : a ⟶ b} -> f ≣ g -> f ≡ g
  open I1Category {{...}} public
    -- field {{equivLevels}} : ∀{a b : X} -> ∀{f g : a ⟶ b} -> IProp (f ≣ g)

module _ {𝒞 : Category 𝑖} {{_ : I1Category 𝒞}} where
  subst-≣ : ∀{a b : ⟨ 𝒞 ⟩} -> (P : (a ⟶ b) -> 𝒰 𝑗) -> {f g : a ⟶ b} -> (f ≣ g) -> P f -> P g
  subst-≣ P e x = subst P (≣→≡ e) x

  -- instance
  --   Cast:≣→≡ : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> Cast (f ≣ g) IAnything (f ≡ g)
  --   Cast.cast Cast:≣→≡ p = ≣→≡ p




