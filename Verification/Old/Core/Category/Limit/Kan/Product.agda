
module Verification.Old.Core.Category.Limit.Kan.Product where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Presheaf
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Instance.SmallCategories
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Category.Proper
open import Verification.Old.Core.Category.Limit.Kan.Definition
open import Verification.Old.Core.Category.Limit.Kan.Terminal
open import Verification.Old.Core.Category.Limit.Kan.Local


-- hasProducts : (𝒞 : Category 𝑖) -> 𝒰 _
-- hasProducts 𝒞 = has(`𝟚`)ShapedLimits 𝒞

-- hasCoproducts : (𝒞 : Category 𝑖) -> 𝒰 _
-- hasCoproducts 𝒞 = has(`𝟚`)ShapedColimits 𝒞

module _ {𝒞 : Category 𝑖} where
  Diagram-𝟚 :  ∀(a b : ⟨ 𝒞 ⟩) -> `𝟚` ⟶ 𝒞
  Diagram-𝟚 a b = free-Diagram-Lift D
    where D : QuiverHom (_) (ForgetCategory 𝒞)
          ⟨ D ⟩ ₀ = a
          ⟨ D ⟩ ₁ = b

  Cone-𝟚 : ∀{D : `𝟚` ⟶ 𝒞} -> ∀{x : ⟨ 𝒞 ⟩} -> (f : x ⟶ ⟨ D ⟩ (↥ ₀)) -> (g : x ⟶ ⟨ D ⟩ (↥ ₁))
           -> ⟨ ! `𝟚` * ⟩ (Diagram-𝟙 x) ⟶ D
  Cone-𝟚 f g = free-Diagram-Nat a (λ {()})
    where a = λ {₀ -> f ; ₁ -> g}

  Cocone-𝟚 : ∀{D : `𝟚` ⟶ 𝒞} -> ∀{x : ⟨ 𝒞 ⟩} -> (f : ⟨ D ⟩ (↥ ₀) ⟶ x) -> (g : ⟨ D ⟩ (↥ ₁) ⟶ x)
           -> D ⟶ ⟨ ! `𝟚` * ⟩ (Diagram-𝟙 x)
  Cocone-𝟚 f g = free-Diagram-Nat a (λ {()})
    where a = λ {₀ -> f ; ₁ -> g}


-- record hasCoproducts-0 (X : 𝒰 𝑖) {{_ : ICategory X 𝑗}} : 𝒰 (𝑖 ､ 𝑗) where


--   infixl 100 _+_
--   _+_ : (a b : ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
--   _+_ a b = colim (Diagram-𝟚 a b)

--   hasCoproduct:+ : ∀{a b : ⟨ 𝒞 ⟩} -> hasCoproduct {𝒞 = 𝒞} a b
--   ⟨ hasCoproduct:+ {a} {b} ⟩ = a + b
--   isCoproduct.ι₀ (of hasCoproduct:+) = ⟨ cocone ⟩ {↥ ₀}
--   isCoproduct.ι₁ (of hasCoproduct:+) = ⟨ cocone ⟩ {↥ ₁}
--   isCoproduct.[_,_] (of hasCoproduct:+) f g = elim-colim (Cocone-𝟚 f g)

-- instance isCoproduct:+ = #openstruct hasCoproduct:+

  -- ι₀ : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ a + b
  -- ι₀ {a} {b} = ⟨ cocone ⟩ {↥ ₀}

  -- ι₁ : ∀{a b : ⟨ 𝒞 ⟩} -> b ⟶ a + b
  -- ι₁ {a} {b} = ⟨ cocone ⟩ {↥ ₁}

  -- a [_,_] : {a b c : ⟨ 𝒞 ⟩} -> (f : a ⟶ c) (g : b ⟶ c) -> (a + b ⟶ c)
  -- a [ f , g ] = elim-colim (Cocone-𝟚 f g)

-- module _ {X : 𝒰 𝑖} {{XX : ICategory X 𝑗}} {{P : hasCoproducts-0 X}} where

-- module _ {𝒞 : Category 𝑖} {{P : hasCoproducts 𝒞}} {{_ : I1Category 𝒞}}  where
--   instance
--     hasCoproducts-1→0 : hasCoproducts-0 𝒞
--     hasCoproducts-0._+_ hasCoproducts-1→0 a b = colim (Diagram-𝟚 a b)
--     isCoproduct.ι₀ (hasCoproducts-0.isCoproduct:+ hasCoproducts-1→0) = ⟨ cocone ⟩ {↥ ₀}
--     isCoproduct.ι₁ (hasCoproducts-0.isCoproduct:+ hasCoproducts-1→0) = ⟨ cocone ⟩ {↥ ₁}
--     isCoproduct.[_,_] (hasCoproducts-0.isCoproduct:+ hasCoproducts-1→0) f g = elim-colim (Cocone-𝟚 f g)

