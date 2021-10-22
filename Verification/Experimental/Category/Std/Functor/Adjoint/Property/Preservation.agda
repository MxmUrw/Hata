
module Verification.Experimental.Category.Std.Functor.Adjoint.Property.Preservation where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Morphism
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Notation.Associativity

open import Verification.Experimental.Category.Std.Functor.Adjoint.Definition
open import Verification.Experimental.Category.Std.Morphism.Epi.Definition

open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Preservation

open import Verification.Experimental.Category.Std.Functor.Adjoint.Property.Base


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} {{_ : F ⊣ G}} where

    --------------------------------------------------------------
    -- Epi preservation
    private
      module _ {a b : ⟨ 𝒞 ⟩} {f : a ⟶ b} where
        lem-1 : isEpi f -> isEpi (map f)
        isEpi.cancel-epi (lem-1 p) {z} {α} {β} q =
              q
              >> map f ◆ α ∼ map f ◆ β <<
              ⟪ construct-postcomp-cofree ⟫
              >> f ◆ cofree α ∼ f ◆ cofree β <<
              ⟪ cancel-epi ⟫
              >> cofree α ∼ cofree β <<
              ⟪ cancel-injective-cofree  ⟫
              >> α ∼ β <<
          where instance _ = p

    isEpiPreserving:byLeftAdjoint : isEpiPreserving F
    isEpiPreserving:byLeftAdjoint = record { preserve-isEpi = lem-1 }

    --------------------------------------------------------------
    -- Coequalizer preservation


    module _ {a b x : ⟨ 𝒞 ⟩}
            {f g : a ⟶ b}
            {{_ : isCoequalizer f g x}} where

      private
        π₌' : ⟨ F ⟩ b ⟶ ⟨ F ⟩ x
        π₌' = map π₌

        equate-π₌' : map f ◆ π₌' ∼ map g ◆ π₌'
        equate-π₌' = equate-π₌
                     >> f ◆ π₌ ∼ g ◆ π₌ <<
                     ⟪ cong-∼ ⟫
                     >> map (f ◆ π₌) ∼ map (g ◆ π₌) <<
                     ⟪ functoriality-◆ ≀∼≀ functoriality-◆ ⟫

        compute-Coeq' : ∀{y} -> (h : ⟨ F ⟩ b ⟶ y) -> (map f ◆ h ∼ map g ◆ h) -> ∑ λ (ξ : ⟨ F ⟩ x ⟶ y) -> π₌' ◆ ξ ∼ h
        compute-Coeq' {y} h p =
          let h' : b ⟶ ⟨ G ⟩ y
              h' = cofree h
              p' : f ◆ h' ∼ g ◆ h'
              p' = construct-postcomp-cofree p

              ξ : x ⟶ ⟨ G ⟩ y
              ξ = ⦗ h' , p' ⦘₌

              ξ' : ⟨ F ⟩ x ⟶ y
              ξ' = free ξ

              lem-2 : π₌' ◆ ξ' ∼ h
              lem-2 = map π₌ ◆ (map ξ ◆ adj _)           ⟨ assoc-r-◆ ⟩-∼
                      (map π₌ ◆ map ξ) ◆ adj _           ⟨ functoriality-◆ ⁻¹ ◈ refl ⟩-∼
                      map (π₌ ◆ ξ) ◆ adj _               ⟨ cong-∼ reduce-π₌ ◈ refl ⟩-∼
                      map h' ◆ adj _                     ⟨ refl ⟩-∼
                      free (cofree h)                  ⟨ inv-free ⟩-∼
                      h                                ∎

          in ξ' , lem-2

        lem-10 : isCoequalizer (map f) (map g) (⟨ F ⟩ x)
        isCoequalizer.π₌ lem-10 = π₌'
        isCoequalizer.equate-π₌ lem-10 = equate-π₌'
        isCoequalizer.compute-Coeq lem-10 = compute-Coeq'
        isCoequalizer.isEpi:π₌ lem-10 = preserve-isEpi (isEpi:π₌)
          where instance _ = isEpiPreserving:byLeftAdjoint

      preservesCoequalizer:byLeftAdjoint : preservesCoequalizer F f g x
      preservesCoequalizer.isCoequalizer:Image preservesCoequalizer:byLeftAdjoint = lem-10
      preservesCoequalizer.preserve-π₌ preservesCoequalizer:byLeftAdjoint = refl

    preservesCoequalizers:byLeftAdjoint : preservesCoequalizers F
    preservesCoequalizers.preservesCoequalizers:this preservesCoequalizers:byLeftAdjoint = preservesCoequalizer:byLeftAdjoint



