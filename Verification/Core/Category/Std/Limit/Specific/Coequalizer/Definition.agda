
module Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono

-- [Hide]
module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  LiftU : (𝒞 -> 𝒰 𝑘) -> (Obj ′ 𝒞 ′ -> 𝒰 𝑘)
  LiftU P o = P ⟨ o ⟩

-- //

-- [Definition]
-- | Let [..] [] be a category.
module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  private variable a b : 𝒞

  -- | A coequalizer |π₌| of a pair of parallel arrows in |𝒞|,
  --   is defined by the following type:
  record isCoequalizer (f g : a ⟶ b) (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    -- | It is given by the following data:
    -- | - A map [..].
    field π₌ : b ⟶ x
    -- | - Such that |f| and |g| become equal when
    --    post composed with |π₌|.
          equate-π₌ : f ◆ π₌ ∼ g ◆ π₌
    -- | - Furthermore, any other arrow which has the same property has to factor through |π₌|.
          compute-Coeq : ∀{c : 𝒞} -> (h : b ⟶ c) -> (p : f ◆ h ∼ g ◆ h) -> ∑ λ (ξ : x ⟶ c) -> π₌ ◆ ξ ∼ h
    -- | - Finally, |π₌| needs to be an epimorphism.
          {{isEpi:π₌}} : isEpi π₌

  -- //

  -- [Hide]


    ⦗_⦘₌ : ∀{c : 𝒞} -> (∑ λ (h : b ⟶ c) -> (f ◆ h ∼ g ◆ h)) -> x ⟶ c
    ⦗_⦘₌ (h , p) = fst (compute-Coeq h p)
    reduce-π₌ : ∀{c : 𝒞} -> {h : b ⟶ c} -> {p : f ◆ h ∼ g ◆ h} -> π₌ ◆ ⦗ h , p ⦘₌ ∼ h
    reduce-π₌ {h = h} {p} = snd (compute-Coeq h p)

  open isCoequalizer {{...}} public

  hasCoequalizer : {a b : 𝒞} (f g : a ⟶ b) -> 𝒰 _
  hasCoequalizer f g = _ :& LiftU (isCoequalizer f g)


  ----------------------------------------------------------
  -- Coequalizer without uniqueness
  record isCoequalizerCandidate {a b : 𝒞} (f g : a ⟶ b) (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field π₌? : b ⟶ x
          equate-π₌? : f ◆ π₌? ∼ g ◆ π₌?

  open isCoequalizerCandidate {{...}} public

  hasCoequalizerCandidate : {a b : 𝒞} (f : HomPair a b) -> 𝒰 _
  hasCoequalizerCandidate (f , g) = _ :& LiftU (isCoequalizerCandidate f g)


record hasCoequalizers (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field Coeq : ∀{a b : ⟨ 𝒞 ⟩} (f g : a ⟶ b) -> ⟨ 𝒞 ⟩
  field {{isCoequalizer:Coeq}} : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> isCoequalizer f g (Coeq f g)

open hasCoequalizers {{...}} public
-- //
