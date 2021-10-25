
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Property.Base where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Epi.Definition

open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Functor




module _ {𝒞 : Category 𝑖} {{_ : hasInitial 𝒞}} where
  module _ {b : ⟨ 𝒞 ⟩} {f g : ⊥ ⟶ b} where

    hasCoequalizer:byInitial : hasCoequalizer f g
    hasCoequalizer:byInitial = b since P
      where
        P : isCoequalizer f g b
        isCoequalizer.π₌ P    = id
        isCoequalizer.equate-π₌ P = expand-⊥ ∙ expand-⊥ ⁻¹
        isCoequalizer.compute-Coeq P = λ h p → h , unit-l-◆
        isCoequalizer.isEpi:π₌ P = isEpi:id

module _ {𝒞 : Category 𝑖} where
  module _ {a b : ⟨ 𝒞 ⟩} {f : a ⟶ b} where
    hasCoequalizer:byId : hasCoequalizer f f
    hasCoequalizer:byId = b since P
      where
        P : isCoequalizer f f b
        isCoequalizer.π₌ P    = id
        isCoequalizer.equate-π₌ P = refl
        isCoequalizer.compute-Coeq P = λ h p → h , unit-l-◆
        isCoequalizer.isEpi:π₌ P = isEpi:id


  module _ {a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} where
    hasCoequalizer:bySym : hasCoequalizer f g -> hasCoequalizer g f
    hasCoequalizer:bySym (x since P) = x since Q
      where
        Q : isCoequalizer g f x
        isCoequalizer.π₌ Q = π₌
        isCoequalizer.equate-π₌ Q = equate-π₌ ⁻¹
        isCoequalizer.compute-Coeq Q = λ h p → compute-Coeq h (p ⁻¹)
        isCoequalizer.isEpi:π₌ Q = isEpi:π₌

  module _ {a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} where
    hasCoequalizerCandidate:bySym : hasCoequalizerCandidate (f , g) -> hasCoequalizerCandidate (g , f)
    hasCoequalizerCandidate:bySym (x since P) = x since Q
      where
        Q : isCoequalizerCandidate g f x
        isCoequalizerCandidate.π₌? Q = π₌?
        isCoequalizerCandidate.equate-π₌? Q = equate-π₌? ⁻¹

module _ {𝒞 : Category 𝑖} where
  module _ {a₀ a₁ b₀ b₁ x₀ x₁ : ⟨ 𝒞 ⟩}
           {f₀ g₀ : a₀ ⟶ b₀} {f₁ g₁ : a₁ ⟶ b₁}
           {{_ : isCoequalizer f₀ g₀ x₀}}
           {{_ : isCoequalizer f₁ g₁ x₁}}
           {{_ : hasCoproducts 𝒞}}
           where

    private
      f₀₁ = map-⊔ (f₀ , f₁)
      g₀₁ = map-⊔ (g₀ , g₁)

    π₌-⊔ : b₀ ⊔ b₁ ⟶ x₀ ⊔ x₁
    π₌-⊔ = map-⊔ (π₌ , π₌)

    equate-π₌-⊔ : f₀₁ ◆ π₌-⊔ ∼ g₀₁ ◆ π₌-⊔
    equate-π₌-⊔ = map-⊔ (f₀ , f₁) ◆ map-⊔ (π₌ , π₌)   ⟨ functoriality-◆ {{isFunctor:⊔}} ⁻¹ ⟩-∼
                  map-⊔ (f₀ ◆ π₌ , f₁ ◆ π₌)           ⟨ cong-∼ (equate-π₌ , equate-π₌) ⟩-∼
                  map-⊔ (g₀ ◆ π₌ , g₁ ◆ π₌)           ⟨ functoriality-◆ {{isFunctor:⊔}} ⟩-∼
                  g₀₁ ◆ π₌-⊔                          ∎

    compute-Coeq-⊔ : ∀{y : ⟨ 𝒞 ⟩} -> (h : b₀ ⊔ b₁ ⟶ y) -> (p : f₀₁ ◆ h ∼ g₀₁ ◆ h) -> ∑ λ (ξ : x₀ ⊔ x₁ ⟶ y) -> π₌-⊔ ◆ ξ ∼ h
    compute-Coeq-⊔ {y} h p =
      let h₀ : b₀ ⟶ y
          h₀ = ι₀ ◆ h

          h₁ : b₁ ⟶ y
          h₁ = ι₁ ◆ h

          p₀ : f₀ ◆ h₀ ∼ g₀ ◆ h₀
          p₀ = p
               >> (f₀₁ ◆ h ∼ g₀₁ ◆ h) <<
               ⟪ (refl ◈_) ⟫
               >> ι₀ ◆ (f₀₁ ◆ h) ∼ ι₀ ◆ (g₀₁ ◆ h) <<
               ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
               >> (ι₀ ◆ f₀₁) ◆ h ∼ (ι₀ ◆ g₀₁) ◆ h <<
               ⟪ reduce-ι₀ ◈ refl ≀∼≀ reduce-ι₀ ◈ refl ⟫
               >> (f₀ ◆ ι₀) ◆ h ∼ (g₀ ◆ ι₀) ◆ h <<
               ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
               >> f₀ ◆ (ι₀ ◆ h) ∼ g₀ ◆ (ι₀ ◆ h) <<

          p₁ : f₁ ◆ h₁ ∼ g₁ ◆ h₁
          p₁ = p
               >> (f₀₁ ◆ h ∼ g₀₁ ◆ h) <<
               ⟪ (refl ◈_) ⟫
               >> ι₁ ◆ (f₀₁ ◆ h) ∼ ι₁ ◆ (g₀₁ ◆ h) <<
               ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
               >> (ι₁ ◆ f₀₁) ◆ h ∼ (ι₁ ◆ g₀₁) ◆ h <<
               ⟪ reduce-ι₁ ◈ refl ≀∼≀ reduce-ι₁ ◈ refl ⟫
               >> (f₁ ◆ ι₁) ◆ h ∼ (g₁ ◆ ι₁) ◆ h <<
               ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
               >> f₁ ◆ (ι₁ ◆ h) ∼ g₁ ◆ (ι₁ ◆ h) <<

          ξ = ⦗ ⦗ h₀ , p₀ ⦘₌ , ⦗ h₁ , p₁ ⦘₌ ⦘

          lem-1 : ι₀ ◆ (π₌-⊔ ◆ ξ) ∼ ι₀ ◆ h
          lem-1 = ι₀ ◆ (π₌-⊔ ◆ ξ)   ⟨ assoc-r-◆ ⟩-∼
                  ι₀ ◆ π₌-⊔ ◆ ξ     ⟨ reduce-ι₀ ◈ refl ⟩-∼
                  (π₌ ◆ ι₀) ◆ ξ     ⟨ assoc-l-◆ ⟩-∼
                  π₌ ◆ (ι₀ ◆ ξ)     ⟨ refl ◈ reduce-ι₀ ⟩-∼
                  π₌ ◆ ⦗ h₀ , p₀ ⦘₌ ⟨ reduce-π₌ ⟩-∼
                  h₀                ∎

          lem-2 : ι₁ ◆ (π₌-⊔ ◆ ξ) ∼ ι₁ ◆ h
          lem-2 = ι₁ ◆ (π₌-⊔ ◆ ξ)   ⟨ assoc-r-◆ ⟩-∼
                  ι₁ ◆ π₌-⊔ ◆ ξ     ⟨ reduce-ι₁ ◈ refl ⟩-∼
                  (π₌ ◆ ι₁) ◆ ξ     ⟨ assoc-l-◆ ⟩-∼
                  π₌ ◆ (ι₁ ◆ ξ)     ⟨ refl ◈ reduce-ι₁ ⟩-∼
                  π₌ ◆ ⦗ h₁ , p₁ ⦘₌ ⟨ reduce-π₌ ⟩-∼
                  h₁                ∎

          lem-3 : π₌-⊔ ◆ ξ ∼ h
          lem-3 = (lem-1 , lem-2)
                  ⟪ cong-∼ {{isSetoidHom:⦗⦘}} ⟫
                  >> ⦗ ι₀ ◆ (π₌-⊔ ◆ ξ) , ι₁ ◆ (π₌-⊔ ◆ ξ) ⦘ ∼ ⦗ ι₀ ◆ h , ι₁ ◆ h ⦘ <<
                  ⟪ expand-⊔ ⁻¹ ≀∼≀ expand-⊔ ⁻¹ ⟫

      in ξ , lem-3

    isEpi:π₌-⊔ : isEpi π₌-⊔
    isEpi:π₌-⊔ = isEpi:map-⊔

    isCoequalizer:⊔ : isCoequalizer (map-⊔ (f₀ , f₁)) (map-⊔ (g₀ , g₁)) (x₀ ⊔ x₁)
    isCoequalizer.π₌ isCoequalizer:⊔ = π₌-⊔
    isCoequalizer.equate-π₌ isCoequalizer:⊔ = equate-π₌-⊔
    isCoequalizer.compute-Coeq isCoequalizer:⊔ = compute-Coeq-⊔
    isCoequalizer.isEpi:π₌ isCoequalizer:⊔ = isEpi:π₌-⊔

