
module Verification.Core.Category.Std.Limit.Specific.Equalizer.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono



module _ {X : 𝒰 𝑖} {{_ : isCategory {𝑗} X}} where
  record isEqualizer {a b : X} (f g : a ⟶ b) (x : X) : 𝒰 (𝑖 ､ 𝑗) where
    field ι₌ : x ⟶ a
    field ∼-ι₌ : ι₌ ◆ f ∼ ι₌ ◆ g
    field ⧼_⧽₌ : ∀{y : X} -> (∑ λ (h : y ⟶ a) -> h ◆ f ∼ h ◆ g) -> y ⟶ x
    field reduce-ι₌ : ∀{y : X} -> {h : y ⟶ a} -> {p : h ◆ f ∼ h ◆ g} -> ⧼ h , p ⧽₌ ◆ ι₌ ∼ h
    field {{isMono:ι₌}} : isMono ι₌


  open isEqualizer {{...}} public

record hasEqualizers (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field Eq : ∀{a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> ⟨ 𝒞 ⟩
  field {{isEqualizer:Eq}} : ∀{a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> isEqualizer f g (Eq f g)

open hasEqualizers {{...}} public

{-
  hasEqualizer : {a b : X} (f g : a ⟶ b) -> 𝒰 _
  hasEqualizer f g = _ :& isEqualizer f g

  -- unquoteDecl hasEqualizer hascoequalizer = #struct "isCoeq" (quote isEqualizer) "x" hasEqualizer hascoequalizer

  record Coeq-ExUniq {a b : X} (f g : a ⟶ b) (x : Obj ′ X ′) :  𝒰 (𝑖 ､ 𝑗) where
    field π-CoeqEU : b ⟶ ⟨ x ⟩
          ∼-CoeqEU : f ◆ π-CoeqEU ∼ g ◆ π-CoeqEU
          elim-CoeqEU : ∀{c : X} -> (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h) -> ⟨ x ⟩ ⟶ c
          reduce-CoeqEU : ∀{d : X} -> (h : b ⟶ d) -> (p : f ◆ h ∼ g ◆ h) -> π-CoeqEU ◆ elim-CoeqEU h p ∼ h
          unique-CoeqEU : ∀{d : X} -> (i j : ⟨ x ⟩ ⟶ d) -> (π-CoeqEU ◆ i ∼ π-CoeqEU ◆ j) -> i ∼ j


  by-CoeqEU-Coeq : {a b : X} {f g : a ⟶ b} {x : Obj ′ X ′} -> Coeq-ExUniq f g x -> isEqualizer f g x
  by-CoeqEU-Coeq {a} {b} {f} {g} {x} record
    { π-CoeqEU = π-CoeqEU ; ∼-CoeqEU = ∼-CoeqEU ; elim-CoeqEU = elim-CoeqEU ; reduce-CoeqEU = reduce-CoeqEU ; unique-CoeqEU = unique-CoeqEU }
    = record
        { π-Coeq = π-CoeqEU
        ; ∼-Coeq = ∼-CoeqEU
        ; elim-Coeq = elim-CoeqEU
        ; reduce-Coeq = reduce-CoeqEU
        ; expand-Coeq = λ i p -> unique-CoeqEU (i) (elim-CoeqEU (π-CoeqEU ◆ i) p) (reduce-CoeqEU (π-CoeqEU ◆ i) p ⁻¹)
        }

record hasEqualizers (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field coeq : ∀{a b : ⟨ 𝒞 ⟩} (f g : a ⟶ b) -> ⟨ 𝒞 ⟩
  field {{isEqualizer:coeq}} : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> isEqualizer f g (obj (coeq f g))

open hasEqualizers {{...}} public
-}
