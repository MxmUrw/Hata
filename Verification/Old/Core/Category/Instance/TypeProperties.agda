
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Instance.TypeProperties where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
-- open import Verification.Old.Core.Category.Limit.Cone.Definition
-- open import Verification.Old.Core.Category.Limit.Cone.Product
-- open import Verification.Old.Core.Category.Limit.Cone.Equalizer
-- open import Verification.Old.Core.Category.Monad
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Quiver

-------------------------
-- Products

-- open has_ShapedLimits
-- open INatural
-- open ICone
-- open ITerminal
-- ⟨ D ⟩ ₀ ×-𝒰 ⟨ D ⟩ ₁

{-
ProductCone : (D : Diagram (⌘ 𝟚) (Category:𝒰 𝑖)) -> Cone D
⟨ ProductCone D ⟩ = ⟨ D ⟩ ₀ ×-𝒰 ⟨ D ⟩ ₁
ICone.▲ (of ProductCone D) {s = ₀} = fst
ICone.▲ (of ProductCone D) {s = ₁} = snd
INatural.naturality (ICone.Natural:▲ (of ProductCone D)) {x = ₀} id-Q = cong (comp-𝒰 fst) (functoriality-id)
INatural.naturality (ICone.Natural:▲ (of ProductCone D)) {x = ₁} id-Q = cong (comp-𝒰 snd) (functoriality-id)
INatural.naturality (ICone.Natural:▲ (of ProductCone D)) (some (last ()))
INatural.naturality (ICone.Natural:▲ (of ProductCone D)) (some (() ∷ x₁))

terminal::ProductCone : ∀{D : Diagram (⌘ 𝟚) (Category:𝒰 𝑖)} -> {c : Cone D} -> ∑ λ (f : c ⟶ ProductCone D) -> ∀(g : c ⟶ ProductCone D) -> g ≣ f
⟨ fst (terminal::ProductCone {D = D} {c}) ⟩ x = ▲ x , ▲ x
IConeHom.▲/ (of fst (terminal::ProductCone {D = D} {c})) {s = ₀} = refl
IConeHom.▲/ (of fst (terminal::ProductCone {D = D} {c})) {s = ₁} = refl
snd (terminal::ProductCone {D = D} {c}) g = λ i a -> (▲/ i a , ▲/ i a)

instance
  hasProducts:𝒰 : hasProducts (𝒰 𝑖)
  ⟨ has_ShapedLimits.lim hasProducts:𝒰 D ⟩ = ProductCone D
  ITerminal.! (of has_ShapedLimits.lim hasProducts:𝒰 D) = fst terminal::ProductCone
  ITerminal.unique (of has_ShapedLimits.lim hasProducts:𝒰 D) = snd terminal::ProductCone

-}

{-
instance
  Absolute-Syntax:∥ : ∀{A : 𝒰 𝑖} -> Absolute-Syntax A ∥ A ∥
  Absolute-Syntax.∣ Absolute-Syntax:∥ ∣ x = ∣ x ∣-Prop

equalize-𝒰 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (f g : A -> B) -> 𝒰 (𝑖 ､ 𝑗)
equalize-𝒰 f g = ∑ λ a -> f a ≡ g a

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} (f g : A -> B) where
  PCone : 𝒰 𝑖 -> 𝒰 _
  PCone Z = ∑ λ (ζ : Z -> A) -> ∀ (z : Z) -> f (ζ z) ≡ g (ζ z)

  P = equalize-𝒰 f g

  !!-PCone : PCone (equalize-𝒰 f g)
  !!-PCone = fst , snd

  module _ {X : 𝒰 𝑖} where
    myeq : (X -> P) -> PCone X
    fst (myeq f) = λ x -> fst (f x)
    snd (myeq f) = λ x -> snd (f x)

    myeq⁻¹ : PCone X -> (X -> P)
    myeq⁻¹ (a , b) = λ x -> a x , b x

  module _  {X : 𝒰 𝑖} {ξ : X -> A} {p : ∀ x -> f (ξ x) ≡ g (ξ x)} where
    ι : equalize-𝒰 f g -> A
    ι = fst

    !! : X -> equalize-𝒰 f g
    !! x = ξ x , p x

    !!-Hom : ∀ x -> ξ x ≡ (ι (!! x))
    !!-Hom x = refl

    module _ (!!2 : X -> equalize-𝒰 f g) (!!2-Hom : ∀ x -> ξ x ≡ ι (!!2 x)) where
      unique!! : ∀ x -> !!2 x ≡ !! x
      unique!! x = {!!}




-- instance
--   hasEqualizers:𝒰 : hasEqualizers (𝒰 𝑖)
--   ⟨ has_ShapedLimits.lim hasEqualizers:𝒰 D ⟩ = let E = equalize-𝒰 ((D ⌄ (₀ , ₁)) ₀) ((D ⌄ (₀ , ₁)) ₁)
--                                                    X = pairCone D E fst (funExt (λ x -> snd x))
--                                                in X
--   ⟨ ITerminal.! (of has_ShapedLimits.lim hasEqualizers:𝒰 D) {a = a} ⟩ x =
--     let P = funExt⁻¹ (lem::⇉-cone-equalizes D a)
--     in (▲ x , P x )
--   IConeHom.▲/ (of ITerminal.! (of has_ShapedLimits.lim hasEqualizers:𝒰 D)) {s = ₀} = refl
--   IConeHom.▲/ (of ITerminal.! (of has_ShapedLimits.lim hasEqualizers:𝒰 D)) {s = ₁} = {!!}
--   ITerminal.unique (of has_ShapedLimits.lim hasEqualizers:𝒰 D) = {!!}

  -- ⟨ ⟨ lim hasEqualizers:𝒰 D ⟩ ⟩ = ∑ λ (a : ⟨ D ⟩ ₀) -> (D ⌄ (₀ , ₁)) ₀ a ≡ (D ⌄ (₀ , ₁)) ₁ a
  -- of ⟨ lim hasEqualizers:𝒰 D ⟩ = {!!}
  -- of (lim hasEqualizers:𝒰 D) = {!!}


-------------------------
-- Sums


-}

