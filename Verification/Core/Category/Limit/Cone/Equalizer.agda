{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Limit.Equalizer where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Adjunction
open import Verification.Core.Category.Limit.Definition

-- === Equalizers

{-

data ⇉ : 𝒰₀ where
  ₀ ₁ : ⇉

instance
  IQuiver:⇉ : IQuiver ⇉ (ℓ₀ , ℓ₀)
  IQuiver.Edge IQuiver:⇉ ₀ ₀ = ⊥
  IQuiver.Edge IQuiver:⇉ ₀ ₁ = 𝟚
  IQuiver.Edge IQuiver:⇉ ₁ b = ⊥
  IQuiver._≈_ IQuiver:⇉ = _≡_
  IQuiver.IEquivInst IQuiver:⇉ = IEquiv:Path

Category:⇉ = Category:Free (⌘ ⇉)




instance
  ICategory:⇉ = of Category:⇉

module _ (X : 𝒰 𝑖) {{_ : ICategory X 𝑗}} where
  open IQuiverHom

  hasEqualizers = has(⌘ ⇉)ShapedLimits X

module _ {X : 𝒰 𝑖} {{_ : ICategory X 𝑗}} where
  pair : {a b : X} (f g : a ⟶ b) -> Functor (⌘ ⇉) (⌘ X)
  pair {a = a} {b} f g = free-Diagram D
    where D : QuiverHom (⌘ ⇉) (ForgetCategory (⌘ X))
          ⟨ D ⟩ ₀ = a
          ⟨ D ⟩ ₁ = b
          IQuiverHom.qmap (of D) {a = ₀} {₁} ₀ = f
          IQuiverHom.qmap (of D) {a = ₀} {₁} ₁ = g

instance
  Index-Notation:Diagram : ∀{S : Quiver (ℓ₀ , ℓ₀ , ℓ₀)} {X : Category 𝑖} -> Index-Notation (Diagram (Category:Free S) X)
                                                                                           (⟨ S ⟩ ×-𝒰 ⟨ S ⟩)
                                                                                           (IAnything)
                                                                                           (λ (D , (a , b)) -> Edge a b -> Hom (⟨ D ⟩ a) (⟨ D ⟩ b))
  (Index-Notation:Diagram Index-Notation.⌄ D) (a , b) e = map (some (last e))

module _ {𝒞 : Category 𝑖} where
  X = ⟨ 𝒞 ⟩
  module _ (D : Diagram (⌘ ⇉) 𝒞) where
    private
      a = ⟨ D ⟩ ₀
      b = ⟨ D ⟩ ₁
      f = ((D ⌄ (₀ , ₁)) ₀)
      g = ((D ⌄ (₀ , ₁)) ₁)
    module _ (x : X) (ξ : x ⟶ a) (p : ξ ◆ f ≣ ξ ◆ g) where

      pairCone : Cone D
      ⟨ pairCone ⟩ = x
      ICone.▲ (of pairCone) {₀} = ξ
      ICone.▲ (of pairCone) {₁} = ξ ◆ f
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {x} {.x} id-Q = (_◈_ {{of 𝒞}} refl functoriality-id) ∙ unit-r-◆ {{of 𝒞}} ∙ sym (unit-l-◆ {{of 𝒞}})
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (last ₀)) = let P : ξ ◆ f ≣ id ◆ (ξ ◆ f)
                                                                                        P = sym (unit-l-◆ {{of 𝒞}})
                                                                                     in P
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (last ₁)) = let P : ξ ◆ g ≣ id ◆ (ξ ◆ f)
                                                                                        P = sym p ∙ (sym (unit-l-◆ {{of 𝒞}}))
                                                                                     in P
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (last ()))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₀ (last ())))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₀ (() ∷ e)))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₁ (last ())))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₁ (() ∷ e)))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₀} () (last x)))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₁} f (last ())))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₀} () (x ∷ e)))
      INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₁} f (() ∷ e)))

    module _ (c : Cone D) where
      private
        x : X
        x = ⟨ c ⟩

        ξ : x ⟶ a
        ξ = ▲

        ξ' : x ⟶ b
        ξ' = ▲

        lem::1 : ξ ◆ f ≣ id ◆ ξ'
        lem::1 = naturality {{Natural:▲ {{of c}}}} (some (last ₀))

        lem::2 : ξ ◆ g ≣ id ◆ ξ'
        lem::2 = naturality {{Natural:▲ {{of c}}}} (some (last ₁))

      lem::⇉-cone-equalizes : ξ ◆ f ≣ ξ ◆ g
      lem::⇉-cone-equalizes = lem::1 ∙ sym lem::2




  -- module _ {a b : X} (f g : a ⟶ b) (x : X) (ξ : x ⟶ a) (p : ξ ◆ f ≣ ξ ◆ g) where
  --   pairCone : Cone (pair f g)
  --   ⟨ pairCone ⟩ = x
  --   ICone.▲ (of pairCone) {₀} = ξ
  --   ICone.▲ (of pairCone) {₁} = ξ ◆ f
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {x} {.x} id-Q = unit-r-◆ {{of 𝒞}} ∙ sym (unit-l-◆ {{of 𝒞}})
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (last ₀)) = let P : ξ ◆ f ≣ id ◆ (ξ ◆ f)
  --                                                                                     P = sym (unit-l-◆ {{of 𝒞}})
  --                                                                                 in P
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (last ₁)) = let P : ξ ◆ g ≣ id ◆ (ξ ◆ f)
  --                                                                                     P = sym p ∙ (sym (unit-l-◆ {{of 𝒞}}))
  --                                                                                 in P
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (last ()))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₀ (last ())))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₀ (() ∷ e)))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₁ (last ())))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₀} (some (_∷_ {b = ₁} ₁ (() ∷ e)))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₀} () (last x)))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₁} f (last ())))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₀} () (x ∷ e)))
  --   INatural.naturality (ICone.Natural:▲ (of pairCone)) {₀} {₁} (some (_∷_ {b = ₁} f (() ∷ e)))

  module _ {{_ : hasEqualizers X}} where

    _=?=_ : {a b : X} (f g : a ⟶ b) -> X
    _=?=_ {a} {b} f g = ⟨ ⟨ lim (pair f g) ⟩ ⟩


-}

