
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono

module _ {X : 𝒰 𝑖} {{_ : isCategory {𝑗} X}} where
  LiftU : (X -> 𝒰 𝑘) -> (Obj ′ X ′ -> 𝒰 𝑘)
  LiftU P o = P ⟨ o ⟩

module _ {X : 𝒰 𝑖} {{_ : isCategory {𝑗} X}} where
  record isCoequalizer {a b : X} (f g : a ⟶ b) (x : X) : 𝒰 (𝑖 ､ 𝑗) where
    field π₌ : b ⟶ x
          equate-π₌ : f ◆ π₌ ∼ g ◆ π₌
          compute-Coeq : ∀{c : X} -> (h : b ⟶ c) -> (p : f ◆ h ∼ g ◆ h) -> ∑ λ (ξ : x ⟶ c) -> π₌ ◆ ξ ∼ h
          {{isEpi:π₌}} : isEpi π₌

          -- expand-Coeq : ∀{c : X} -> {h : x ⟶ c} -> {p : f ◆ (π₌ ◆ h) ∼ g ◆ (π₌ ◆ h)} -> h ∼ ⦗_⦘₌ (π₌ ◆ h) p
          -- (assoc-r-◆ ∙ (equate-π₌ ◈ refl) ∙ assoc-l-◆)

    ⦗_⦘₌ : ∀{c : X} -> (∑ λ (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h)) -> x ⟶ c
    ⦗_⦘₌ (h , p) = fst (compute-Coeq h p)
    reduce-π₌ : ∀{c : X} -> {h : b ⟶ c} -> {p : f ◆ h ∼ g ◆ h} -> π₌ ◆ ⦗ h , p ⦘₌ ∼ h
    reduce-π₌ {h = h} {p} = snd (compute-Coeq h p)

  open isCoequalizer {{...}} public


  hasCoequalizer : {a b : X} (f g : a ⟶ b) -> 𝒰 _
  hasCoequalizer f g = _ :& LiftU (isCoequalizer f g)

  -- unquoteDecl hasCoequalizer hascoequalizer = #struct "isCoeq" (quote isCoequalizer) "x" hasCoequalizer hascoequalizer

  -- record Coeq-ExUniq {a b : X} (f g : a ⟶ b) (x : Obj ′ X ′) :  𝒰 (𝑖 ､ 𝑗) where
  --   field π₌EU : b ⟶ x
  --         equate-π₌EU : f ◆ π₌EU ∼ g ◆ π₌EU
  --         ⦗_⦘₌EU : ∀{c : X} -> (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h) -> x ⟶ c
  --         reduce-π₌EU : ∀{d : X} -> (h : b ⟶ d) -> (p : f ◆ h ∼ g ◆ h) -> π₌EU ◆ ⦗_⦘₌EU h p ∼ h
  --         unique-CoeqEU : ∀{d : X} -> (i j : x ⟶ d) -> (π₌EU ◆ i ∼ π₌EU ◆ j) -> i ∼ j


  -- by-CoeqEU-Coeq : {a b : X} {f g : a ⟶ b} {x : Obj ′ X ′} -> Coeq-ExUniq f g x -> isCoequalizer f g x
  -- by-CoeqEU-Coeq {a} {b} {f} {g} {x} record
  --   { π₌EU = π₌EU ; equate-π₌EU = equate-π₌EU ; ⦗_⦘₌EU = ⦗_⦘₌EU ; reduce-π₌EU = reduce-π₌EU ; unique-CoeqEU = unique-CoeqEU }
  --   = record
  --       { π₌ = π₌EU
  --       ; equate-π₌ = equate-π₌EU
  --       ; ⦗_⦘₌ = ⦗_⦘₌EU
  --       ; reduce-π₌ = reduce-π₌EU
  --       ; expand-Coeq = λ i p -> unique-CoeqEU (i) (⦗_⦘₌EU (π₌EU ◆ i) p) (reduce-π₌EU (π₌EU ◆ i) p ⁻¹)
  --       }

record hasCoequalizers (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field Coeq : ∀{a b : ⟨ 𝒞 ⟩} (f g : a ⟶ b) -> ⟨ 𝒞 ⟩
  field {{isCoequalizer:Coeq}} : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> isCoequalizer f g (Coeq f g)

open hasCoequalizers {{...}} public

