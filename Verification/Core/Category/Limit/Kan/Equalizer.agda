

module Verification.Core.Category.Limit.Kan.Equalizer where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Functor.Adjunction
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Lift
open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Kan.Terminal

-- module _ {𝒞 : Category 𝑖} where





hasEqualizers : Category 𝑖 -> 𝒰 𝑖
hasEqualizers = has(𝔼)ShapedLimits
module _ {𝒞 : Category 𝑖} where
  Diagram-𝔼 :  ∀{a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> 𝔼 ⟶ 𝒞
  Diagram-𝔼 {a = a} {b} f g = free-Diagram-Lift D
      where D : QuiverHom Quiver:Pair (ForgetCategory 𝒞)
            ⟨ D ⟩ ₀ = a
            ⟨ D ⟩ ₁ = b
            IQuiverHom.qmap (of D) arr₀ = f
            IQuiverHom.qmap (of D) arr₁ = g

  -- module _ {{_ : hasEqualizers 𝒞}} where
  Cone-𝔼 : {D : 𝔼 ⟶ 𝒞} -> ∀{x : ⟨ 𝒞 ⟩} -> (f : x ⟶ ⟨ D ⟩ (↥ ₀)) -> (p : f ◆ map ` arr₀ ` ≣ f ◆ map ` arr₁ `) -> ⟨ ! 𝔼 * ⟩ (Diagram-𝟙 x) ⟶ D
  Cone-𝔼 f p = free-Diagram-Nat X (λ {arr₀ -> unit-l-◆ ⁻¹;
                                        arr₁ -> p ⁻¹ ∙ unit-l-◆ ⁻¹})
    where X = λ {₀ -> f ;
                  ₁ -> f ◆ map ` arr₀ `}

module _ {𝒞 : Category 𝑖} {{_ : hasEqualizers 𝒞}}  where
  Eq : ∀{a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> ⟨ 𝒞 ⟩
  Eq f g = lim (Diagram-𝔼 f g)





