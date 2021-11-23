
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{_ : hasCoproducts ′ 𝒞 ′ }} where
-- {{_ : FiniteCoproductCategory 𝑖 on 𝒞}} where

  private
    𝒞' : Category _
    𝒞' = ′ 𝒞 ′

  map-⊔ : ∀{a b c d : 𝒞} -> (a ⟶ b) × (c ⟶ d) -> (a ⊔ c ⟶ b ⊔ d)
  map-⊔ (f , g) = ⦗ f ◆ ι₀ , g ◆ ι₁ ⦘

  infixl 100 _⇃⊔⇂_
  _⇃⊔⇂_ : ∀{a b c d : 𝒞} -> (a ⟶ b) -> (c ⟶ d) -> (a ⊔ c ⟶ b ⊔ d)
  _⇃⊔⇂_ = λ₊ map-⊔

  private instance
    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:⦗⦘

  _≀⇃⊔⇂≀_ : ∀{a b c d : 𝒞} -> {f g : a ⟶ b} {h i : c ⟶ d}
            -> (f ∼ g) -> (h ∼ i)
            -> (f ⇃⊔⇂ h) ∼ (g ⇃⊔⇂ i)
  _≀⇃⊔⇂≀_ {f = f} {g} {h} {i} p q =
    let
        lem-1 : ⦗ f ◆ ι₀ , h ◆ ι₁ ⦘ ∼ ⦗ g ◆ ι₀ , i ◆ ι₁ ⦘
        lem-1 = cong-∼ ((p ◈ refl ) , q ◈ refl)

    in lem-1


  private instance
    isSetoidHom:map-⊔ : ∀{a b c d : 𝒞} -> isSetoidHom ′((a ⟶ b) ×-𝒰 (c ⟶ d))′ (a ⊔ c ⟶ b ⊔ d) (map-⊔)
    isSetoidHom:map-⊔ = record { cong-∼ = λ (p , q) → p ≀⇃⊔⇂≀ q }

  functoriality-id-⊔ : ∀{a b : 𝒞} -> map-⊔ (id {a = a} , id {a = b}) ∼ id
  functoriality-id-⊔ {a} {b} = P
    where
      ida : a ⟶ a
      ida = id

      idb : b ⟶ b
      idb = id

      idab : (a ⊔ b) ⟶ (a ⊔ b)
      idab = id

      P = ⦗ ida ◆ ι₀ , idb ◆ ι₁ ⦘    ⟨ cong-∼ (unit-l-◆ ∙ unit-r-◆ ⁻¹ , unit-l-◆ ∙ unit-r-◆ ⁻¹) ⟩-∼
          ⦗ ι₀ ◆ idab , ι₁ ◆ idab ⦘  ⟨ expand-ι₀,ι₁ ⁻¹ ⟩-∼
          idab                       ∎

  append-⇃⊔⇂ : ∀{a0 a1 b0 b1 x : 𝒞}
                -> {f0 : a0 ⟶ a1} -> {f1 : a1 ⟶ x}
                -> {g0 : b0 ⟶ b1} -> {g1 : b1 ⟶ x}
                -> (f0 ⇃⊔⇂ g0) ◆ ⦗ f1 , g1 ⦘ ∼ ⦗ f0 ◆ f1 , g0 ◆ g1 ⦘
  append-⇃⊔⇂ {f0 = f0} {f1} {g0} {g1} =
    ⦗ f0 ◆ ι₀ , g0 ◆ ι₁ ⦘ ◆ ⦗ f1 , g1 ⦘          ⟨ expand-ι₀,ι₁ ⟩-∼
    ⦗ ι₀ ◆ (⦗ f0 ◆ ι₀ , g0 ◆ ι₁ ⦘ ◆ ⦗ f1 , g1 ⦘)
    , ι₁ ◆ (⦗ f0 ◆ ι₀ , g0 ◆ ι₁ ⦘ ◆ ⦗ f1 , g1 ⦘) ⦘ ⟨ cong-∼ (( assoc-r-◆ ∙ (reduce-ι₀ ◈ refl))
                                                            , assoc-r-◆ ∙ (reduce-ι₁ ◈ refl)) ⟩-∼

    ⦗ ((f0 ◆ ι₀) ◆ ⦗ f1 , g1 ⦘)
    , ((g0 ◆ ι₁) ◆ ⦗ f1 , g1 ⦘) ⦘                  ⟨ cong-∼ ( (assoc-l-◆ ∙ (refl ◈ reduce-ι₀))
                                                            , ((assoc-l-◆ ∙ (refl ◈ reduce-ι₁)))) ⟩-∼
    ⦗ f0 ◆ f1 , g0 ◆ g1 ⦘                        ∎



  functoriality-◆-⊔ : ∀{a0 a1 a2 b0 b1 b2 : 𝒞}
                      -> {f0 : a0 ⟶ a1} -> {f1 : a1 ⟶ a2}
                      -> {g0 : b0 ⟶ b1} -> {g1 : b1 ⟶ b2}
                      -> ((f0 ◆ f1) ⇃⊔⇂ (g0 ◆ g1)) ∼ (f0 ⇃⊔⇂ g0) ◆ (f1 ⇃⊔⇂ g1)
  functoriality-◆-⊔ {f0 = f0} {f1} {g0} {g1} =
    ((f0 ◆ f1) ⇃⊔⇂ (g0 ◆ g1))                  ⟨ cong-∼ (assoc-l-◆ , assoc-l-◆) ⟩-∼
    ⦗ f0 ◆ (f1 ◆ ι₀) , g0 ◆ (g1 ◆ ι₁) ⦘        ⟨ append-⇃⊔⇂ ⁻¹ ⟩-∼
    (f0 ⇃⊔⇂ g0) ◆ ⦗ f1 ◆ ι₀ , g1 ◆ ι₁ ⦘        ∎-∼

  -- instance
  isFunctor:⊔ : isFunctor (𝒞' ×-𝐂𝐚𝐭 𝒞') 𝒞' (λ₋ _⊔_)
  isFunctor.map isFunctor:⊔               = map-⊔
  isFunctor.isSetoidHom:map isFunctor:⊔   = isSetoidHom:map-⊔
  isFunctor.functoriality-id isFunctor:⊔  = functoriality-id-⊔
  isFunctor.functoriality-◆ isFunctor:⊔   = functoriality-◆-⊔


  --------------------------------------------------------------
  -- properties

  module _ {a b c d : 𝒞} {f : a ⟶ b} {g : c ⟶ d} where
    module _ {{_ : isEpi f}} {{_ : isEpi g}} where
      isEpi:map-⊔ : isEpi (map-⊔ (f , g))
      isEpi.cancel-epi isEpi:map-⊔ {α = α} {β} p =
        let
          functoriality-id-⊔ : ι₀ ◆ α ∼ ι₀ ◆ β
          functoriality-id-⊔ = p
               ⟪ (refl ◈_) ⟫
               >> ι₀ ◆ (map-⊔ (f , g) ◆ α) ∼ ι₀ ◆ (map-⊔ (f , g) ◆ β) <<
               ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
               >> (ι₀ ◆ map-⊔ (f , g)) ◆ α ∼ (ι₀ ◆ map-⊔ (f , g)) ◆ β <<
               ⟪ reduce-ι₀ ◈ refl ≀∼≀ reduce-ι₀ ◈ refl ⟫
               >> (f ◆ ι₀) ◆ α ∼ (f ◆ ι₀) ◆ β <<
               ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
               >> f ◆ (ι₀ ◆ α) ∼ f ◆ (ι₀ ◆ β) <<
               ⟪ cancel-epi ⟫

          lem-2 : ι₁ ◆ α ∼ ι₁ ◆ β
          lem-2 = p
               ⟪ (refl ◈_) ⟫
               >> ι₁ ◆ (map-⊔ (f , g) ◆ α) ∼ ι₁ ◆ (map-⊔ (f , g) ◆ β) <<
               ⟪ assoc-r-◆ ≀∼≀ assoc-r-◆ ⟫
               >> (ι₁ ◆ map-⊔ (f , g)) ◆ α ∼ (ι₁ ◆ map-⊔ (f , g)) ◆ β <<
               ⟪ reduce-ι₁ ◈ refl ≀∼≀ reduce-ι₁ ◈ refl ⟫
               >> (g ◆ ι₁) ◆ α ∼ (g ◆ ι₁) ◆ β <<
               ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
               >> g ◆ (ι₁ ◆ α) ∼ g ◆ (ι₁ ◆ β) <<
               ⟪ cancel-epi ⟫

          lem-3 : α ∼ β
          lem-3 = (functoriality-id-⊔ , lem-2)
                  ⟪ cong-∼ {{isSetoidHom:⦗⦘}} ⟫
                  >> ⦗ ι₀ ◆ α , ι₁ ◆ α ⦘ ∼ ⦗ ι₀ ◆ β , ι₁ ◆ β ⦘ <<
                  ⟪ expand-ι₀,ι₁ ⁻¹ ≀∼≀ expand-ι₀,ι₁ ⁻¹ ⟫

        in lem-3

