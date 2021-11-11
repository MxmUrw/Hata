
module Verification.Old.Core.Category.Limit.Specific.Coequalizer where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Cat


module _ {X : 𝒰 𝑖} {{_ : isCategory X 𝑗}} where
  record isCoequalizer {a b : X} (f g : a ⟶ b) (x : X) : 𝒰 (𝑖 ､ 𝑗) where
    field π-Coeq : b ⟶ x
          ≣-Coeq : f ◆ π-Coeq ≣ g ◆ π-Coeq
          elim-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (f ◆ h ≣ g ◆ h) -> x ⟶ c
          reduce-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (p : f ◆ h ≣ g ◆ h)
                        -> π-Coeq ◆ elim-Coeq h p ≣ h
          expand-Coeq : ∀{c : X} -> (h : x ⟶ c) -> (p : f ◆ (π-Coeq ◆ h) ≣ g ◆ (π-Coeq ◆ h)) -> h ≣ elim-Coeq (π-Coeq ◆ h) p
          -- (assoc-r-◆ ∙ (≣-Coeq ◈ refl) ∙ assoc-l-◆)

open isCoequalizer {{...}} public
unquoteDecl hasCoequalizer hascoequalizer = #struct "isCoeq" (quote isCoequalizer) "x" hasCoequalizer hascoequalizer




