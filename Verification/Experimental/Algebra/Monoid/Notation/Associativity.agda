
module Verification.Core.Algebra.Monoid.Notation.Associativity where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition


module _ {M : 𝒰 _} {{_ : Monoid 𝑗 on M}} where
  assoc-[ab][cd]∼a[bc]d-⋆ : {f g h i : M}
                            -> (f ⋆ g) ⋆ (h ⋆ i) ∼ f ⋆ (g ⋆ h) ⋆ i
  assoc-[ab][cd]∼a[bc]d-⋆ {f = f} {g} {h} {i} =
    (f ⋆ g) ⋆ (h ⋆ i)    ⟨ assoc-r-⋆ ⟩-∼
    (f ⋆ g) ⋆ h ⋆ i      ⟨ assoc-l-⋆ ≀⋆≀ refl ⟩-∼
    f ⋆ (g ⋆ h) ⋆ i      ∎

  assoc-[abcd]∼a[bcd]-⋆ : {f g h i : M}
                          -> f ⋆ g ⋆ h ⋆ i ∼ f ⋆ (g ⋆ h ⋆ i)
  assoc-[abcd]∼a[bcd]-⋆ {f = f} {g} {h} {i} =
    f ⋆ g ⋆ h ⋆ i     ⟨ assoc-l-⋆ ⟩-∼
    f ⋆ g ⋆ (h ⋆ i)   ⟨ assoc-l-⋆ ⟩-∼
    f ⋆ (g ⋆ (h ⋆ i)) ⟨ refl ≀⋆≀ assoc-r-⋆ ⟩-∼
    f ⋆ (g ⋆ h ⋆ i)   ∎

  assoc-[abcd]∼a[bc]d-⋆ : {f g h i : M}
                            -> f ⋆ g ⋆ h ⋆ i ∼ f ⋆ (g ⋆ h) ⋆ i
  assoc-[abcd]∼a[bc]d-⋆ {f = f} {g} {h} {i} = assoc-l-⋆ ≀⋆≀ refl
