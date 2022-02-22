
{-# OPTIONS --experimental-lossy-unification #-}

-- NOTE
-- This file only typechecks with --experimental-lossy-unification,
-- because at some places unification of morphisms in 𝐅𝐮𝐥𝐥 would
-- need annotations otherwise.
-- With --experimental-lossy-unification, we do not need those.
--

module Verification.Core.Data.FiniteIndexed.Instance.ExternallyFinitelyAtomic where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Discrete
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
open import Verification.Core.Data.List.Variant.Binary.Element.Properties
-- open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Category.Construction.Coproduct
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Functor.Representable2
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed

-- open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated
open import Verification.Core.Category.Std.Category.Structured.Atomic.Variant.ExternallyFinitelyAtomic.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition


module _ {I : 𝒰 𝑖} where
  𝑠𝑖𝑛𝑔𝑙 : I -> 𝐅𝐢𝐧𝐈𝐱 I
  𝑠𝑖𝑛𝑔𝑙 i = incl (incl i)

  private
    lem-0 : ∀{a : I} {u : 𝐅𝐢𝐧𝐈𝐱 I} -> ⟨ ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟩ -> ix (ι u) a
    lem-0 f = ⟨ f ⟩ _ incl

    cong-lem-0 : ∀{a : I} {u : 𝐅𝐢𝐧𝐈𝐱 I} -> {f g : ⟨ ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟩} -> f ∼ g -> lem-0 f ≡ lem-0 g
    cong-lem-0 (incl p) = λ i → p _ i incl

    lem-1 : ∀{a : I} {u : 𝐅𝐢𝐧𝐈𝐱 I} -> ix (ι u) a -> ⟨ ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟩
    lem-1 ap = incl (λ {i incl → ap})

    cong-lem-1 : ∀{a : I} {u : 𝐅𝐢𝐧𝐈𝐱 I} -> {x y : ix (ι u) a} -> x ≡ y -> lem-1 x ∼ lem-1 y
    cong-lem-1 ap = incl (λ {a i incl → ap i})

    inverse-◆-l-lem-0 : ∀{a : I} {u : 𝐅𝐢𝐧𝐈𝐱 I} -> {f : ⟨ ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟩} -> lem-1 (lem-0 f) ∼ f
    inverse-◆-l-lem-0 {a} {u} {f} = incl (λ {a i incl → ⟨ f ⟩ _ incl})

  module _ {𝑗 : 𝔏 ^ 3} {a : I} where
    isAtom:𝑠𝑖𝑛𝑔𝑙 : isAtom 𝑗 (𝑠𝑖𝑛𝑔𝑙 a)
    isAtom:𝑠𝑖𝑛𝑔𝑙 = record { preserve-isCoproduct = P }
      where

        Q : ∀{u v : 𝐅𝐢𝐧𝐈𝐱 I} -> isCoproduct (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v))
        Q {u} {v} = Res
          where

            ι₀' : (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u) ⟶ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v))
            ι₀' = (λ a -> lem-1 (⟨ ι₀ ⟩ _ (lem-0 a)))
                  since
                  record { cong-∼ = λ {p → cong-lem-1 (cong (⟨ ι₀ ⟩ _) (cong-lem-0 p))} }

            ι₁' : (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v) ⟶ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v))
            ι₁' = (λ a -> lem-1 (⟨ ι₁ ⟩ _ (lem-0 a)))
                  since
                  record { cong-∼ = λ {p → cong-lem-1 (cong (⟨ ι₁ ⟩ _) (cong-lem-0 p))} }

            module Elim {z : 𝐒𝐭𝐝 _} (f : ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟶ z) (g : ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v ⟶ z) where
              ξᵘ : ⟨ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟩ -> ⟨ z ⟩
              ξᵘ h with lem-0 h
              ... | left-∍  h  = ⟨ f ⟩ (lem-1 h)
              ... | right-∍ h  = ⟨ g ⟩ (lem-1 h)

              cong-ξ : {a b : ⟨ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟩} -> (p : a ∼ b) -> ξᵘ a ∼ ξᵘ b
              cong-ξ {a} {b} p with lem-0 a | lem-0 b | cong-lem-0 p
              ... | right-∍ a | right-∍ b | p = cong-∼ {{of g}} (cong-lem-1 (cancel-injective-𝒰 p))
              ... | right-∍ a | left-∍ b  | p = impossible p
              ... | left-∍ a  | right-∍ b | p = impossible p
              ... | left-∍ a  | left-∍ b  | p = cong-∼ {{of f}} (cong-lem-1 (cancel-injective-𝒰 p))


              ξ : (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟶ z
              ξ = ξᵘ since record { cong-∼ = cong-ξ }

              reduce-ι₀' : ι₀' ◆ ξ ∼ f
              reduce-ι₀' = pointwise λ h -> p
                where
                  p : ∀{h : Hom-𝐅𝐮𝐥𝐥 (𝑠𝑖𝑛𝑔𝑙 a) u} -> ξᵘ (⟨ ι₀' ⟩ h) ∼ ⟨ f ⟩ h
                  p {h} = cong-∼ {{of f}} inverse-◆-l-lem-0

              reduce-ι₁' : ι₁' ◆ ξ ∼ g
              reduce-ι₁' = pointwise (λ h -> cong-∼ {{of g}} inverse-◆-l-lem-0)

            expand'-ι₀,ι₁ : ∀{z : 𝐒𝐭𝐝 _} -> {k : (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟶ z} -> k ∼ (Elim.ξ (ι₀' ◆ k) (ι₁' ◆ k))
            expand'-ι₀,ι₁ {z} {k} = pointwise lem-12
              where
                lem-11 : ∀(h : ⟨ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟩) -> ⟨ k ⟩ (lem-1 (lem-0 h)) ∼ ⟨ (Elim.ξ (ι₀' ◆ k) (ι₁' ◆ k)) ⟩ h
                lem-11 h with lem-0 h
                ... | right-∍ X = refl
                ... | left-∍ X = refl

                lem-12 : ∀(h : ⟨ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟩) -> ⟨ k ⟩ h ∼ ⟨ (Elim.ξ (ι₀' ◆ k) (ι₁' ◆ k)) ⟩ h
                lem-12 h = cong-∼ {{of k}} (inverse-◆-l-lem-0) ⁻¹ ∙ lem-11 h

            ⦗_⦘' : ∀{z : 𝐒𝐭𝐝 _} -> (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟶ z) × (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v ⟶ z) -> (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ⟶ z
            ⦗_⦘' {z} (f , g) = Elim.ξ f g

            cong-ξ : ∀{z : 𝐒𝐭𝐝 _} -> {f₀ f₁ : ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u ⟶ z} -> {g₀ g₁ : ⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v ⟶ z}
                     -> f₀ ∼ f₁ -> g₀ ∼ g₁ -> Elim.ξ f₀ g₀ ∼ Elim.ξ f₁ g₁
            cong-ξ {z} {f₀} {f₁} {g₀} {g₁} p q = pointwise lem-12
              where
                lem-12 : ∀(h) -> ⟨ Elim.ξ f₀ g₀ ⟩ h ∼ ⟨ Elim.ξ f₁ g₁ ⟩ h
                lem-12 h with lem-0 h
                ... | left-∍ X   = ⟨ p ⟩ _
                ... | right-∍ X  = ⟨ q ⟩ _


            Res : isCoproduct (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v))
            isCoproduct.ι₀ Res = ι₀'
            isCoproduct.ι₁ Res = ι₁'
            isCoproduct.⦗ Res ⦘ = ⦗_⦘'
            isCoproduct.reduce-ι₀ Res {z} {f} {g} = Elim.reduce-ι₀' f g
            isCoproduct.reduce-ι₁ Res {z} {f} {g} = Elim.reduce-ι₁' f g
            isCoproduct.expand-ι₀,ι₁ Res = expand'-ι₀,ι₁
            isCoproduct.isSetoidHom:⦗⦘ Res = record { cong-∼ = λ (p , q) -> cong-ξ p q }


        P : ∀{u v x : 𝐅𝐢𝐧𝐈𝐱 I} -> isCoproduct u v x -> isCoproduct (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)
        P {u} {v} {x} isCoproduct:x = lem-14
          where
            instance _ = isCoproduct:x

            lem-11 : u ⊔ v ≅ x
            lem-11 = ≅:byIsCoproduct

            lem-12 : isCoproduct (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v))
            lem-12 = Q

            lem-13 : (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ (u ⊔ v)) ≅ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)
            lem-13 = congOf-≅ (ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a)) lem-11

            lem-14 : isCoproduct (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ u) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ v) (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)
            lem-14 = transp-≅-Coproduct lem-13 {{lem-12}}


