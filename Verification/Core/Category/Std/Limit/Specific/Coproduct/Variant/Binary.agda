
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Notation.Associativity

infixr 20 _[_]→2_
_[_]→2_ : ∀{𝑗} (X : 𝒰 𝑗) -> ∀ (𝑖 : 𝔏 ^ 2) -> (R : 𝒰 𝑙) -> (𝒰 _)
_[_]→2_ {𝑗 = 𝑗} X 𝑖 R = {U : 𝒰 (𝑖 ⌄ 0)} -> (u : U) -> {{UU : hasU U (𝑗) (𝑖 ⌄ 1)}} -> {{p : getU UU ≡-Str (X)}} -> R
-- _[_]→2_ {𝑗 = 𝑗} X 𝑖 R = {U : 𝒰 (𝑖 ⌄ 0)} -> (u : UniverseHintWrapper U) -> {{UU : hasU U (𝑗) (𝑖 ⌄ 1)}} -> {{p : getU UU ≡-Str (X)}} -> R

macro
  _×2_ : ∀{𝑖 𝑗 : 𝔏} {𝑘 𝑙 : 𝔏 ^ 2} -> (𝒰' 𝑖) [ 𝑙 ]→2 (𝒰' 𝑗) [ 𝑘 ]→2 SomeStructure
  _×2_ = λstr A ↦ λstr B ↦ #structureOn (A ×-𝒰 B)
  infixr 40 _×2_


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where


  record isInitial (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field elim-⊥ : ∀{a} -> x ⟶ a
    field expand-⊥ : ∀{a} -> {f : x ⟶ a} -> f ∼ elim-⊥

  open isInitial {{...}} public


  record isCoproduct (a b x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field ι₀ : a ⟶ x
    field ι₁ : b ⟶ x
    field ⦗_⦘ : ∀{c} -> ((a ⟶ c) × (b ⟶ c)) -> x ⟶ c
    field {{isSetoidHom:⦗⦘}} : ∀{c} -> isSetoidHom ′((a ⟶ c) ×-𝒰 (b ⟶ c))′ (x ⟶ c) (⦗_⦘ {c})
    field reduce-ι₀ : ∀{c} {f : a ⟶ c} {g : b ⟶ c} -> ι₀ ◆ ⦗ f , g ⦘ ∼ f
    field reduce-ι₁ : ∀{c} {f : a ⟶ c} {g : b ⟶ c} -> ι₁ ◆ ⦗ f , g ⦘ ∼ g
    field expand-ι₀,ι₁  : ∀{c} {f : x ⟶ c} -> f ∼ ⦗ ι₀ ◆ f , ι₁ ◆ f ⦘

  open isCoproduct {{...}} public
  {-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
  {-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
  {-# DISPLAY isCoproduct.⦗_⦘ _ x = ⦗ x ⦘ #-}


  module _ {a b x y : 𝒞} (p : x ≅ y) {{_ : isCoproduct a b x}} where

    private
      ι₀' : a ⟶ y
      ι₀' = ι₀ ◆ ⟨ p ⟩

      ι₁' : b ⟶ y
      ι₁' = ι₁ ◆ ⟨ p ⟩

      ⦗_⦘' : ∀{z} -> ∀(p : ((a ⟶ z) × (b ⟶ z))) -> y ⟶ z
      ⦗_⦘' = λ (f , g) → ⟨ sym-≅ p ⟩ ◆ ⦗ f , g ⦘

      lem-1 : ∀{z} -> isSetoidHom ′((a ⟶ z) ×-𝒰 (b ⟶ z))′ (y ⟶ z) ⦗_⦘'
      lem-1 = record { cong-∼ = λ p → refl ◈ cong-∼ p}

      lem-2 : ∀{z} -> {f : (a ⟶ z)} -> {g : (b ⟶ z)} -> ι₀' ◆ ⦗ f , g ⦘' ∼ f
      lem-2 {f = f} {g} = (ι₀ ◆ ⟨ p ⟩) ◆ (⟨ sym-≅ p ⟩ ◆ ⦗ f , g ⦘)   ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⟩-∼
                          ι₀ ◆ (⟨ p ⟩ ◆ ⟨ sym-≅ p ⟩) ◆ ⦗ f , g ⦘     ⟨ refl ◈ inv-r-◆ (of p) ◈ refl ⟩-∼
                          ι₀ ◆ id ◆ ⦗ f , g ⦘                        ⟨ unit-r-◆ ◈ refl ⟩-∼
                          ι₀ ◆ ⦗ f , g ⦘                             ⟨ reduce-ι₀ ⟩-∼
                          f                                         ∎

    transp-≅-Coproduct : isCoproduct a b y
    isCoproduct.ι₀ transp-≅-Coproduct             = ι₀'
    isCoproduct.ι₁ transp-≅-Coproduct             = ι₁'
    isCoproduct.⦗ transp-≅-Coproduct ⦘            = ⦗_⦘'
    isCoproduct.isSetoidHom:⦗⦘ transp-≅-Coproduct = lem-1
    isCoproduct.reduce-ι₀ transp-≅-Coproduct      = lem-2
    isCoproduct.reduce-ι₁ transp-≅-Coproduct      = {!!}
    isCoproduct.expand-ι₀,ι₁ transp-≅-Coproduct       = {!!}

  module _ {a b x y : 𝒞} {{_ : isCoproduct a b x}} {{_ : isCoproduct a b y}} where
    ≅:byIsCoproduct : x ≅ y
    ≅:byIsCoproduct = f since P
      where
        f : x ⟶ y
        f = ⦗ ι₀ , ι₁ ⦘

        g : y ⟶ x
        g = ⦗ ι₀ , ι₁ ⦘

        lem-1 : f ◆ g ∼ id
        lem-1 = f ◆ g                           ⟨ expand-ι₀,ι₁ ⟩-∼
                ⦗ ι₀ ◆ (f ◆ g) , ι₁ ◆ (f ◆ g) ⦘ ⟨ cong-∼ (assoc-r-◆ , assoc-r-◆) ⟩-∼
                ⦗ (ι₀ ◆ f) ◆ g , (ι₁ ◆ f) ◆ g ⦘ ⟨ cong-∼ (reduce-ι₀ ◈ refl , reduce-ι₁ ◈ refl) ⟩-∼
                ⦗ ι₀ ◆ g , ι₁ ◆ g ⦘             ⟨ cong-∼ (reduce-ι₀ , reduce-ι₁) ⟩-∼
                ⦗ ι₀ , ι₁ ⦘                     ⟨ cong-∼ (unit-r-◆ ⁻¹ , unit-r-◆ ⁻¹) ⟩-∼
                ⦗ ι₀ ◆ id , ι₁ ◆ id ⦘           ⟨ expand-ι₀,ι₁ ⁻¹ ⟩-∼
                id                              ∎


        lem-2 : g ◆ f ∼ id
        lem-2 = g ◆ f                           ⟨ expand-ι₀,ι₁ ⟩-∼
                ⦗ ι₀ ◆ (g ◆ f) , ι₁ ◆ (g ◆ f) ⦘ ⟨ cong-∼ (assoc-r-◆ , assoc-r-◆) ⟩-∼
                ⦗ (ι₀ ◆ g) ◆ f , (ι₁ ◆ g) ◆ f ⦘ ⟨ cong-∼ (reduce-ι₀ ◈ refl , reduce-ι₁ ◈ refl) ⟩-∼
                ⦗ ι₀ ◆ f , ι₁ ◆ f ⦘             ⟨ cong-∼ (reduce-ι₀ , reduce-ι₁) ⟩-∼
                ⦗ ι₀ , ι₁ ⦘                     ⟨ cong-∼ (unit-r-◆ ⁻¹ , unit-r-◆ ⁻¹) ⟩-∼
                ⦗ ι₀ ◆ id , ι₁ ◆ id ⦘           ⟨ expand-ι₀,ι₁ ⁻¹ ⟩-∼
                id                              ∎

        P : isIso (hom f)
        P = record { inverse-◆ = g ; inv-r-◆ = lem-1 ; inv-l-◆ = lem-2 }



record hasInitial (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field ⊥ : ⟨ 𝒞 ⟩
  field {{isInitial:⊥}} : isInitial ⊥

open hasInitial {{...}} public

record hasCoproducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  infixl 80 _⊔_
  field _⊔_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field {{isCoproduct:⊔}} : ∀{a b} -> isCoproduct a b (a ⊔ b)

open hasCoproducts {{...}} public
{-# DISPLAY hasCoproducts._⊔_ _ x y = x ⊔ y #-}

record hasFiniteCoproducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field {{hasInitial:this}} : hasInitial 𝒞
  field {{hasCoproducts:this}}    : hasCoproducts 𝒞

open hasFiniteCoproducts {{...}} public

module _ {𝒞 : Category 𝑖} {{_ : hasCoproducts 𝒞}} {{_ : hasInitial 𝒞}} where
  hasFiniteCoproducts:default : hasFiniteCoproducts 𝒞
  hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:default  = it
  hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:default     = it


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
  macro
    ⊔⃨ : SomeStructure
    ⊔⃨ = #structureOn (λ₋ _⊔_)

module _ {𝒞ᵘ : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞ᵘ}} {{_ : hasCoproducts ′ 𝒞ᵘ ′ }} where

  private macro 𝒞 = #structureOn 𝒞ᵘ
  private instance _ = isSetoidHom:⦗⦘

  append-⦗⦘ : ∀{a b c d : 𝒞} {f : a ⟶ c} {g : b ⟶ c} {h : c ⟶ d}
            -> ⦗ f , g ⦘ ◆ h ∼ ⦗ f ◆ h , g ◆ h ⦘
  append-⦗⦘ {f = f} {g} {h} =
    ⦗ f , g ⦘ ◆ h                                     ⟨ expand-ι₀,ι₁ ⟩-∼
    ⦗ ι₀ ◆ (⦗ f , g ⦘ ◆ h) , ι₁ ◆ (⦗ f , g ⦘ ◆ h) ⦘   ⟨ cong-∼ ( (assoc-r-◆ ∙ (reduce-ι₀ ◈ refl))
                                                               , (assoc-r-◆ ∙ (reduce-ι₁ ◈ refl))) ⟩-∼
    ⦗ f ◆ h , g ◆ h ⦘                                 ∎


