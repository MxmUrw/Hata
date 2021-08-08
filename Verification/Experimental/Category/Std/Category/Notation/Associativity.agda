
module Verification.Experimental.Category.Std.Category.Notation.Associativity where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  assoc-[ab][cd]∼a[bc]d-◆ : ∀{a b c d e : 𝒞}
                            -> {f : a ⟶ b} -> {g : b ⟶ c} -> {h : c ⟶ d} -> {i : d ⟶ e}
                            -> (f ◆ g) ◆ (h ◆ i) ∼ f ◆ (g ◆ h) ◆ i
  assoc-[ab][cd]∼a[bc]d-◆ {f = f} {g} {h} {i} =
    (f ◆ g) ◆ (h ◆ i)    ⟨ assoc-r-◆ ⟩-∼
    (f ◆ g) ◆ h ◆ i      ⟨ assoc-l-◆ ◈ refl ⟩-∼
    f ◆ (g ◆ h) ◆ i      ∎

