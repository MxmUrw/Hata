
module Verification.Core.Category.Std.Functor.Instance.Monoidal where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Algebra.Monoid.Definition



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  private instance
    _ : isSetoid ⟨ 𝒟 ⟩
    _ = isSetoid:byCategory

  module _ {{isMonoidal:𝒟 : isMonoidal 𝒟}} where

    infixl 70 _⊗-𝐅𝐮𝐧𝐜_

    _⊗-𝐅𝐮𝐧𝐜_ : (F G : 𝐅𝐮𝐧𝐜 𝒞 𝒟) -> 𝐅𝐮𝐧𝐜 𝒞 𝒟
    _⊗-𝐅𝐮𝐧𝐜_ F G = H since lem-1
      where
        H = (λ x -> ⟨ F ⟩ x ⊗ ⟨ G ⟩ x)

        lem-1 : isFunctor 𝒞 𝒟 H
        isFunctor.map lem-1               = λ f → map (map f , map f)
        isFunctor.isSetoidHom:map lem-1   = record { cong-∼ = λ p → cong-∼ (cong-∼ p , cong-∼ p) }
        isFunctor.functoriality-id lem-1  =
          map (map id , map id)           ⟨ cong-∼ (functoriality-id , functoriality-id) ⟩-∼
          map (id , id)                   ⟨ functoriality-id ⟩-∼
          id {{of 𝒟}}                     ∎
        isFunctor.functoriality-◆ lem-1 {f = f} {g} =
          map (map (f ◆ g) , map (f ◆ g))           ⟨ cong-∼ (functoriality-◆ , functoriality-◆) ⟩-∼
          map (map f ◆ map g , map f ◆ map g)       ⟨ functoriality-◆ ⟩-∼
          map (map f , map f) ◆ map (map g , map g) ∎


    𝖨𝖽-𝐅𝐮𝐧𝐜 : 𝐅𝐮𝐧𝐜 𝒞 𝒟
    𝖨𝖽-𝐅𝐮𝐧𝐜 = const ◌ since lem-1
      where
        lem-1 : isFunctor 𝒞 𝒟 (const ◌)
        isFunctor.map lem-1              = λ f → id
        isFunctor.isSetoidHom:map lem-1  = record { cong-∼ = λ p → refl }
        isFunctor.functoriality-id lem-1 = refl
        isFunctor.functoriality-◆ lem-1  = unit-2-◆ ⁻¹

    _⇃⊗⇂-𝐅𝐮𝐧𝐜_ : {F₀ F₁ G₀ G₁ : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> (α : F₀ ⟶ F₁) (β : G₀ ⟶ G₁) -> ((F₀ ⊗-𝐅𝐮𝐧𝐜 G₀) ⟶ (F₁ ⊗-𝐅𝐮𝐧𝐜 G₁))
    _⇃⊗⇂-𝐅𝐮𝐧𝐜_ {F₀} {F₁} {G₀} {G₁} α β = c since P
      where
        c : ∀{x : ⟨ 𝒞 ⟩} -> ⟨ F₀ ⟩ x ⊗ ⟨ G₀ ⟩ x ⟶ ⟨ F₁ ⟩ x ⊗ ⟨ G₁ ⟩ x
        c = map (⟨ α ⟩ , ⟨ β ⟩)

        P : isNatural _ _ c
        P = natural (λ f ->
              let Q : c ◆ (map (map f , map f)) ∼ (map (map f , map f)) ◆ c
                  Q = c ◆ map (map f , map f)                ⟨ functoriality-◆ ⁻¹ ⟩-∼
                      map (⟨ α ⟩ ◆ map f , ⟨ β ⟩ ◆ map f)     ⟨ cong-∼ (naturality f , naturality f) ⟩-∼
                      map (map f ◆ ⟨ α ⟩ , map f ◆ ⟨ β ⟩)     ⟨ functoriality-◆ ⟩-∼
                      map (map f , map f) ◆ c                ∎
              in Q
            )


    instance
      isFunctor:⊗-𝐅𝐮𝐧𝐜 : isFunctor (𝐅𝐮𝐧𝐜 𝒞 𝒟 ×-𝐂𝐚𝐭 𝐅𝐮𝐧𝐜 𝒞 𝒟) (𝐅𝐮𝐧𝐜 𝒞 𝒟) (λ₋ _⊗-𝐅𝐮𝐧𝐜_)
      isFunctor.map isFunctor:⊗-𝐅𝐮𝐧𝐜              = λ (α , β) -> α ⇃⊗⇂-𝐅𝐮𝐧𝐜 β
      isFunctor.isSetoidHom:map isFunctor:⊗-𝐅𝐮𝐧𝐜  = record { cong-∼ = λ (p , q) → cong-∼ (p , q) }
      isFunctor.functoriality-id isFunctor:⊗-𝐅𝐮𝐧𝐜 = functoriality-id
      isFunctor.functoriality-◆ isFunctor:⊗-𝐅𝐮𝐧𝐜  = functoriality-◆

    private
      lem-10 : ∀{F : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> (𝖨𝖽-𝐅𝐮𝐧𝐜 ⊗-𝐅𝐮𝐧𝐜 F) ∼ F
      lem-10 {F} = α since P
        where
          α : Natural (𝖨𝖽-𝐅𝐮𝐧𝐜 ⊗-𝐅𝐮𝐧𝐜 F) F
          α = ⟨ unit-l-⋆ ⟩ since natural (λ _ → naturality _)

          β : Natural F (𝖨𝖽-𝐅𝐮𝐧𝐜 ⊗-𝐅𝐮𝐧𝐜 F)
          β = ⟨ unit-l-⋆ ⁻¹ ⟩ since natural (λ f → naturality _)

          P : isIso (hom α)
          P = record
              { inverse-◆ = β
              ; inv-r-◆   = inv-r-◆ (of unit-l-⋆)
              ; inv-l-◆   = inv-l-◆ (of unit-l-⋆)
              }

      -- lem-11 : isNaturalIso (⧼ Const 𝖨𝖽-𝐅𝐮𝐧𝐜 , id ⧽ ◆ ′ λ₋ _⊗-𝐅𝐮𝐧𝐜_ ′) id lem-10
      -- lem-11 = naturalIso (λ f {_} → naturality ⟨ f ⟩
      --          ) (λ f {_} → naturality ⟨ f ⟩)

      lem-20 : ∀{F : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> (F ⊗-𝐅𝐮𝐧𝐜 𝖨𝖽-𝐅𝐮𝐧𝐜) ∼ F
      lem-20 {F} = α since P
        where
          α : Natural (F ⊗-𝐅𝐮𝐧𝐜 𝖨𝖽-𝐅𝐮𝐧𝐜) F
          α = ⟨ unit-r-⋆ ⟩ since natural (λ _ → naturality _)

          β : Natural F (F ⊗-𝐅𝐮𝐧𝐜 𝖨𝖽-𝐅𝐮𝐧𝐜)
          β = ⟨ unit-r-⋆ ⁻¹ ⟩ since natural (λ f → naturality _)

          P : isIso (hom α)
          P = record
              { inverse-◆ = β
              ; inv-r-◆   = inv-r-◆ (of unit-r-⋆)
              ; inv-l-◆   = inv-l-◆ (of unit-r-⋆)
              }

      lem-30 : ∀{F G H : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> ((F ⊗-𝐅𝐮𝐧𝐜 G) ⊗-𝐅𝐮𝐧𝐜 H) ∼ (F ⊗-𝐅𝐮𝐧𝐜 (G ⊗-𝐅𝐮𝐧𝐜 H))
      lem-30 {F} {G} {H} = α since P
        where
          α : Natural ((F ⊗-𝐅𝐮𝐧𝐜 G) ⊗-𝐅𝐮𝐧𝐜 H) (F ⊗-𝐅𝐮𝐧𝐜 (G ⊗-𝐅𝐮𝐧𝐜 H))
          α = ⟨ assoc-l-⋆ ⟩ since natural (λ _ -> naturality _)

          β : Natural (F ⊗-𝐅𝐮𝐧𝐜 (G ⊗-𝐅𝐮𝐧𝐜 H)) ((F ⊗-𝐅𝐮𝐧𝐜 G) ⊗-𝐅𝐮𝐧𝐜 H)
          β = ⟨ assoc-l-⋆ ⁻¹ ⟩ since natural (λ _ -> naturality _)

          P : isIso (hom α)
          P = record
              { inverse-◆ = β
              ; inv-r-◆   = inv-r-◆ (of assoc-l-⋆)
              ; inv-l-◆   = inv-l-◆ (of assoc-l-⋆)
              }




    instance
      isMonoid:𝐅𝐮𝐧𝐜 : isMonoid (𝐅𝐮𝐧𝐜 𝒞 𝒟)
      isMonoid:𝐅𝐮𝐧𝐜 = record
                        { _⋆_        = _⊗-𝐅𝐮𝐧𝐜_
                        ; ◌          = 𝖨𝖽-𝐅𝐮𝐧𝐜
                        ; unit-l-⋆   = lem-10
                        ; unit-r-⋆   = lem-20
                        ; assoc-l-⋆  = lem-30
                        ; _≀⋆≀_ = λ p q -> cong-≅ (into-×-≅ p q)
                        }

    instance
      isMonoidal:𝐅𝐮𝐧𝐜 : isMonoidal (𝐅𝐮𝐧𝐜 𝒞 𝒟)
      isMonoidal.isMonoid:this           isMonoidal:𝐅𝐮𝐧𝐜 = isMonoid:𝐅𝐮𝐧𝐜
      isMonoidal.isFunctor:⋆             isMonoidal:𝐅𝐮𝐧𝐜 = isFunctor:⊗-𝐅𝐮𝐧𝐜
      isMonoidal.isNaturalIso:unit-l-⋆   isMonoidal:𝐅𝐮𝐧𝐜 = naturalIso (λ f {_} -> naturality ⟨ f ⟩) (λ f {_} -> naturality ⟨ f ⟩)
      isMonoidal.isNaturalIso:unit-r-⋆   isMonoidal:𝐅𝐮𝐧𝐜 = naturalIso (λ f {_} -> naturality ⟨ f ⟩) (λ f {_} -> naturality ⟨ f ⟩)
      isMonoidal.compat-Monoidal-⋆       isMonoidal:𝐅𝐮𝐧𝐜 = λ p q {_} -> refl
      isMonoidal.isNaturalIso:assoc-l-⋆  isMonoidal:𝐅𝐮𝐧𝐜 = naturalIso (λ f {_} -> naturality _) (λ f {_} -> naturality _)
      isMonoidal.triangle-Monoidal       isMonoidal:𝐅𝐮𝐧𝐜 = triangle-Monoidal
      isMonoidal.pentagon-Monoidal       isMonoidal:𝐅𝐮𝐧𝐜 = pentagon-Monoidal
{-
-}

