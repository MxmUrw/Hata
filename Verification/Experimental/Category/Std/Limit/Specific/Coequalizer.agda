
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition

module _ {X : 𝒰 𝑖} {{_ : isCategory 𝑗 X}} where
  record isCoequalizer {a b : X} (f g : a ⟶ b) (x : X) : 𝒰 (𝑖 ､ 𝑗) where
    field π-Coeq : b ⟶ x
          ∼-Coeq : f ◆ π-Coeq ∼ g ◆ π-Coeq
          elim-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h) -> x ⟶ c
          reduce-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (p : f ◆ h ∼ g ◆ h)
                        -> π-Coeq ◆ elim-Coeq h p ∼ h
          expand-Coeq : ∀{c : X} -> (h : x ⟶ c) -> (p : f ◆ (π-Coeq ◆ h) ∼ g ◆ (π-Coeq ◆ h)) -> h ∼ elim-Coeq (π-Coeq ◆ h) p
          -- (assoc-r-◆ ∙ (∼-Coeq ◈ refl) ∙ assoc-l-◆)

  open isCoequalizer {{...}} public
  -- hasCoequalizer : {a b : X} (f g : a ⟶ b) -> 𝒰 _
  -- hasCoequalizer

  unquoteDecl hasCoequalizer hascoequalizer = #struct "isCoeq" (quote isCoequalizer) "x" hasCoequalizer hascoequalizer

  record Coeq-ExUniq {a b : X} (f g : a ⟶ b) (x : X) :  𝒰 (𝑖 ､ 𝑗) where
    field π-CoeqEU : b ⟶ x
          ∼-CoeqEU : f ◆ π-CoeqEU ∼ g ◆ π-CoeqEU
          elim-CoeqEU : ∀{c : X} -> (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h) -> x ⟶ c
          reduce-CoeqEU : ∀{d : X} -> (h : b ⟶ d) -> (p : f ◆ h ∼ g ◆ h) -> π-CoeqEU ◆ elim-CoeqEU h p ∼ h
          unique-CoeqEU : ∀{d : X} -> (i j : x ⟶ d) -> (π-CoeqEU ◆ i ∼ π-CoeqEU ◆ j) -> i ∼ j


  by-CoeqEU-Coeq : {a b : X} {f g : a ⟶ b} {x : X} -> Coeq-ExUniq f g x -> isCoequalizer f g x
  by-CoeqEU-Coeq {a} {b} {f} {g} {x} record
    { π-CoeqEU = π-CoeqEU ; ∼-CoeqEU = ∼-CoeqEU ; elim-CoeqEU = elim-CoeqEU ; reduce-CoeqEU = reduce-CoeqEU ; unique-CoeqEU = unique-CoeqEU }
    = record
        { π-Coeq = π-CoeqEU
        ; ∼-Coeq = ∼-CoeqEU
        ; elim-Coeq = elim-CoeqEU
        ; reduce-Coeq = reduce-CoeqEU
        ; expand-Coeq = λ i p -> unique-CoeqEU (i) (elim-CoeqEU (π-CoeqEU ◆ i) p) (reduce-CoeqEU (π-CoeqEU ◆ i) p ⁻¹)
        }




