
module Verification.Experimental.Category.Std.Morphism.Iso.Property where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Faithful
open import Verification.Experimental.Category.Std.Functor.Full
open import Verification.Experimental.Set.Setoid.Morphism

open import Verification.Experimental.Category.Std.Morphism.Iso.Definition

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  module _ {F : ⟨ 𝒞 ⟩ -> ⟨ 𝒟 ⟩} {{_ : isFunctor 𝒞 𝒟 F}} where


    cong-≅ : ∀{a b : ⟨ 𝒞 ⟩} -> (a ≅ b) -> F a ≅ F b
    cong-≅ p = q₀ since P
      where
        q₀ = map ⟨ p ⟩
        q₁ = map (inverse-◆ (of p))

        P₀ : q₀ ◆ q₁ ∼ id
        P₀ = map ⟨ p ⟩ ◆ map (inverse-◆ (of p))   ⟨ functoriality-◆ ⁻¹ ⟩-∼
             map (⟨ p ⟩ ◆ inverse-◆ (of p))       ⟨ cong-∼ (inv-r-◆ (of p)) ⟩-∼
             map id                               ⟨  functoriality-id ⟩-∼
             id {{of 𝒟}}                         ∎

        P₁ : q₁ ◆ q₀ ∼ id
        P₁ = map (inverse-◆ (of p)) ◆ map ⟨ p ⟩   ⟨ functoriality-◆ ⁻¹ ⟩-∼
             map (inverse-◆ (of p) ◆ ⟨ p ⟩)       ⟨ cong-∼ (inv-l-◆ (of p)) ⟩-∼
             map id                               ⟨  functoriality-id ⟩-∼
             id {{of 𝒟}}                         ∎

        P : isIso (hom q₀)
        P = record
            { inverse-◆  = q₁
            ; inv-r-◆    = P₀
            ; inv-l-◆    = P₁
            }

    module _ where
      private
        instance
          _ : isSetoid ⟨ 𝒞 ⟩
          _ = isSetoid:byCategory

          _ : isSetoid ⟨ 𝒟 ⟩
          _ = isSetoid:byCategory

      isSetoidHom:byFunctor : isSetoidHom ′ ⟨ 𝒞 ⟩ ′ ′ ⟨ 𝒟 ⟩ ′ F
      isSetoidHom:byFunctor = record { cong-∼ = cong-≅ }

    module _ {{_ : isFull ′ F ′}} {{_ : isFaithful ′ F ′}} where
      cong⁻¹-≅ : ∀{a b : ⟨ 𝒞 ⟩} -> F a ≅ F b -> (a ≅ b)
      cong⁻¹-≅ {a} {b} f = f' since Q
        where
          f' : a ⟶ b
          f' = surj ⟨ f ⟩

          g' : b ⟶ a
          g' = surj (inverse-◆ (of f))

          lem-1 : f' ◆ g' ∼ id
          lem-1 = inv-r-◆ (of f)
                  >> ⟨ f ⟩ ◆ inverse-◆ (of f) ∼ id <<
                  ⟪ (inv-surj ⁻¹ ◈ inv-surj ⁻¹) ≀∼≀ refl ⟫
                  >> map f' ◆ map g' ∼ id <<
                  ⟪ (functoriality-◆ ⁻¹) ≀∼≀ (functoriality-id ⁻¹) ⟫
                  >> map (f' ◆ g') ∼ map id <<
                  ⟪ cancel-injective ⟫


          lem-2 : g' ◆ f' ∼ id
          lem-2 = inv-l-◆ (of f)
                  >> inverse-◆ (of f) ◆ ⟨ f ⟩ ∼ id <<
                  ⟪ (inv-surj ⁻¹ ◈ inv-surj ⁻¹) ≀∼≀ refl ⟫
                  >> map g' ◆ map f' ∼ id <<
                  ⟪ (functoriality-◆ ⁻¹) ≀∼≀ (functoriality-id ⁻¹) ⟫
                  >> map (g' ◆ f') ∼ map id <<
                  ⟪ cancel-injective ⟫

          Q = record
              { inverse-◆ = g'
              ; inv-r-◆   = lem-1
              ; inv-l-◆   = lem-2
              }
