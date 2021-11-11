
module Verification.Core.Category.Std.Category.Instance.CategoryLike where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Morphism.Iso


macro
  𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
  𝐂𝐚𝐭 𝑖 = #structureOn (Category 𝑖)


module _ {𝒞 : Category 𝑖} where
  id-𝐂𝐚𝐭 : Functor 𝒞 𝒞
  id-𝐂𝐚𝐭 = ′ id-𝒰 ′
    where instance
            isFunctor:id : isFunctor 𝒞 𝒞 id-𝒰
            isFunctor.map isFunctor:id = id-𝒰
            isFunctor.isSetoidHom:map isFunctor:id = record { cong-∼ = λ x → x }
            isFunctor.functoriality-id isFunctor:id = refl
            isFunctor.functoriality-◆ isFunctor:id = refl

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {𝒢 : Category 𝑘} where
  infixl 50 _◆-𝐂𝐚𝐭_
  _◆-𝐂𝐚𝐭_ : (Functor 𝒞 𝒟) -> Functor 𝒟 𝒢 -> Functor 𝒞 𝒢
  _◆-𝐂𝐚𝐭_ F G = ′ ⟨ F ⟩ ◆-𝒰 ⟨ G ⟩ ′
    where instance
            isFunctor:◆ : isFunctor 𝒞 𝒢 (⟨ F ⟩ ◆-𝒰 ⟨ G ⟩)
            isFunctor.map isFunctor:◆ f             = map (map {{of F}} f)
            isFunctor.isSetoidHom:map isFunctor:◆   = record { cong-∼ = λ p -> cong-∼ (cong-∼ p) }
            isFunctor.functoriality-id isFunctor:◆  = cong-∼ functoriality-id ∙ functoriality-id
            isFunctor.functoriality-◆ isFunctor:◆   = cong-∼ functoriality-◆ ∙ functoriality-◆

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  unit-l-◆-𝐂𝐚𝐭 : ∀{F : Functor 𝒞 𝒟} -> id-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F ∼ F
  unit-l-◆-𝐂𝐚𝐭 {F} = α since P
    where
      α : id-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F ⟶ F
      α = (λ x → id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹)

      β : F ⟶ id-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F
      β = (λ x → id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹)

      P = record
          { inverse-◆ = β
          ; inv-r-◆ = componentwise (λ x → unit-2-◆)
          ; inv-l-◆ = componentwise (λ x → unit-2-◆)
          }

  unit-r-◆-𝐂𝐚𝐭 : ∀{F : Functor 𝒞 𝒟} -> F ◆-𝐂𝐚𝐭 id-𝐂𝐚𝐭 ∼ F
  unit-r-◆-𝐂𝐚𝐭 {F} = α since P
    where
      α : F ◆-𝐂𝐚𝐭 id-𝐂𝐚𝐭 ⟶ F
      α = (λ x → id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹)

      β : F ⟶ F ◆-𝐂𝐚𝐭 id-𝐂𝐚𝐭
      β = (λ x → id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹)

      P = record
          { inverse-◆ = β
          ; inv-r-◆ = componentwise (λ x → unit-2-◆)
          ; inv-l-◆ = componentwise (λ x → unit-2-◆)
          }


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} {ℱ : Category 𝑙} where
  module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 ℰ} {H : Functor ℰ ℱ} where
    assoc-l-◆-𝐂𝐚𝐭 : (F ◆-𝐂𝐚𝐭 G ◆-𝐂𝐚𝐭 H) ∼ F ◆-𝐂𝐚𝐭 (G ◆-𝐂𝐚𝐭 H)
    assoc-l-◆-𝐂𝐚𝐭 = α since P
      where
        α : (F ◆-𝐂𝐚𝐭 G ◆-𝐂𝐚𝐭 H) ⟶ F ◆-𝐂𝐚𝐭 (G ◆-𝐂𝐚𝐭 H)
        α = (λ x → id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹)

        β : F ◆-𝐂𝐚𝐭 (G ◆-𝐂𝐚𝐭 H) ⟶ (F ◆-𝐂𝐚𝐭 G ◆-𝐂𝐚𝐭 H)
        β = (λ x → id) since natural (λ f → unit-l-◆ ∙ unit-r-◆ ⁻¹)

        P = record
            { inverse-◆ = β
            ; inv-r-◆ = componentwise (λ x → unit-2-◆)
            ; inv-l-◆ = componentwise (λ x → unit-2-◆)
            }


