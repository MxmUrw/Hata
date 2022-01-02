
module Verification.Core.Theory.Std.Inference.Definition where

open import Verification.Conventions hiding (ℕ)

open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


record Infer (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  constructor incl
  field ⟨_⟩ : 大𝐌𝐧𝐝 𝑖

open Infer public

module _ (𝑖 : 𝔏 ^ 3) where
  macro 𝐈𝐧𝐟𝐞𝐫 = #structureOn (Infer 𝑖)

record isInferHom {b a : Infer 𝑖} (f : ⟨ b ⟩ ⟶ ⟨ a ⟩) : 𝒰 𝑖 where
  field inferF : fst ⟨ a ⟩ ⟶ fst ⟨ b ⟩
  field infer : (↳ snd ⟨ a ⟩) ⟶ ((↳ snd ⟨ a ⟩) ◆ ((inferF ◆ ((↳ snd ⟨ b ⟩) ◆ fst f))))
  field eval-infer : inferF ◆-𝐂𝐚𝐭 fst f ⟶ id

open isInferHom public

SubcategoryData-Infer : SubcategoryData (大𝐌𝐧𝐝 𝑖) (Infer 𝑖)
SubcategoryData-Infer = subcatdata ⟨_⟩ isInferHom

open ShortMonadNotation

isInferHom:id : ∀{a : Infer 𝑖} -> isInferHom (idOn ⟨ a ⟩)
isInferHom:id {a = a} = record
  { inferF = id
  -- ; infer = (λ x → map (pure x)) since natural {!!}

  ; infer = ⟨ unit-r-◆ ⟩⁻¹ ◆ _⇃◆⇂_ {f₀ = ↳ snd ⟨ a ⟩} {f₁ = ↳ snd ⟨ a ⟩} {g₀ = id-𝐂𝐚𝐭} {g₁ = id-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 ((↳ snd ⟨ a ⟩) ◆-𝐂𝐚𝐭 fst (idOn ⟨ a ⟩))}
                             id
                             (⟨ unit-l-◆ ⟩⁻¹ ◆ _⇃◆⇂_ {f₀ = id-𝐂𝐚𝐭} {f₁ = id-𝐂𝐚𝐭} {g₀ = id-𝐂𝐚𝐭} {g₁ = (↳ snd ⟨ a ⟩) ◆-𝐂𝐚𝐭 fst (idOn ⟨ a ⟩)}
                                               id
                                               (pure since natural naturality))

  ; eval-infer = (λ x → id) since natural (λ f → {!!})
  }

instance
  isSubcategory:Infer : isSubcategory (SubcategoryData-Infer {𝑖 = 𝑖})
  isSubcategory:Infer = record
    { closed-◆ = {!!}
    ; closed-id = isInferHom:id
    }

instance
  isCategory:𝐈𝐧𝐟𝐞𝐫 : isCategory (𝐈𝐧𝐟𝐞𝐫 𝑖)
  isCategory:𝐈𝐧𝐟𝐞𝐫 = isCategory:bySubcategory


module _ {a b : 𝐈𝐧𝐟𝐞𝐫 𝑖} where
  runaround : (f : b ⟶ a) -> (↳ snd ⟨ a ⟩) ⟶ (↳ snd ⟨ a ⟩)
  runaround f = infer (goodHom f)
                ◆ (_⇃◆⇂_ {f₀ = (↳ snd ⟨ a ⟩)} {f₁ = (↳ snd ⟨ a ⟩)} {g₀ = (inferF (goodHom f) ◆ ((↳ snd ⟨ b ⟩) ◆ fst ⟨ f ⟩))} {g₁ = (↳ snd ⟨ a ⟩)}
                  id (_⇃◆⇂_ {f₀ = inferF (goodHom f)} {f₁ = inferF (goodHom f)} {g₀ = ((↳ snd ⟨ b ⟩) ◆-𝐂𝐚𝐭 fst ⟨ f ⟩)} {g₁ = fst ⟨ f ⟩ ◆-𝐂𝐚𝐭 (↳ snd ⟨ a ⟩)}
                            id
                            (snd ⟨ f ⟩)
                     ◆ ( ⟨ assoc-r-◆ {{isCategory:Category}} {f = inferF (goodHom f)} {g = (fst ⟨ f ⟩)} {h = (↳ snd ⟨ a ⟩)} ⟩ ◆
                          (_⇃◆⇂_ {f₀ = inferF (goodHom f) ◆-𝐂𝐚𝐭 (fst ⟨ f ⟩)} {f₁ = id-𝐂𝐚𝐭} {g₀ = (↳ snd ⟨ a ⟩)} {g₁ = (↳ snd ⟨ a ⟩)}
                                (eval-infer (goodHom f)) id)
                       ◆ ⟨ unit-l-◆ {{isCategory:Category}} ⟩))
                  ◆ μ)

-- {!!} ⇃◆⇂ id


-- module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
--   module _ {A : 𝒰 𝑖} where
--     ⨆ᶠ : ∀{as : ⋆List A} -> ([ as ]ᶠ -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
--     ⨆ᶠ = {!!}


-- module _ {𝒞 : Category 𝑖} where
--   instance
--     isCategory:Monad : isCategory {⨆ 𝑖 , ⨆ 𝑖} (Monad 𝒞)
--     isCategory:Monad = {!!}


-- module _ {I : 𝒰 𝑖} where
--   instance
--     isCategory:FinitaryRelativeMonad : isCategory {𝑖 , 𝑖} (FinitaryRelativeMonad I)
--     isCategory:FinitaryRelativeMonad = {!!}

-- module _ (I : 𝒰 𝑖) where
--   macro 𝐅𝐢𝐧𝐑𝐞𝐥𝐌𝐧𝐝 = #structureOn (FinitaryRelativeMonad I)


-- 𝑖𝑥mnd : 𝒰 𝑖 -> Category _
-- 𝑖𝑥mnd {𝑖} I = 𝐅𝐢𝐧𝐑𝐞𝐥𝐌𝐧𝐝 (I)

-- map-𝑖𝑥mnd : ∀{a b : 𝒰 𝑖} -> (a → b) → Functor (𝑖𝑥mnd b) (𝑖𝑥mnd a)
-- map-𝑖𝑥mnd = {!!}

-- instance
--   isFunctor:𝑖𝑥mnd : isFunctor (𝐔𝐧𝐢𝐯 𝑖 ᵒᵖ) (𝐂𝐚𝐭 _) 𝑖𝑥mnd
--   isFunctor.map isFunctor:𝑖𝑥mnd = map-𝑖𝑥mnd
--   isFunctor.isSetoidHom:map isFunctor:𝑖𝑥mnd = {!!}
--   isFunctor.functoriality-id isFunctor:𝑖𝑥mnd = {!!}
--   isFunctor.functoriality-◆ isFunctor:𝑖𝑥mnd = {!!}

{-
module _ (𝑖 : 𝔏) where
  𝐈𝐱𝐌𝐧𝐝ᵘ : 𝒰 _
  𝐈𝐱𝐌𝐧𝐝ᵘ = ⨊ᵒᵖ ′ 𝑖𝑥mnd {𝑖} ′

  macro 𝐈𝐱𝐌𝐧𝐝 = #structureOn 𝐈𝐱𝐌𝐧𝐝ᵘ


open import Agda.Primitive using (lsuc)

module _ (J : 𝒰 𝑗) where
  record hasPseudoInverse2 {𝑖 : 𝔏} (a b : 𝐈𝐱𝐌𝐧𝐝 𝑖) : 𝒰 (join-𝔏 (𝑖 ⁺) 𝑗) where
    -- field testaa : (Indexed (J) (𝒰 𝑖 since isCategory:𝒰)) -> (Indexed (J) (𝒰 𝑖 since {!!}))
    field PIErr : Functor (𝐈𝐱 (base a) (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖))

-- module _ (J : 𝒰 𝑗) where
--   record hasPseudoInverse {𝑖 : 𝔏} {a b : 𝐈𝐱𝐌𝐧𝐝 𝑖} (f : a ⟶ b) : 𝒰 (join-𝔏 (lsuc 𝑖) 𝑗) where
--     field testaa : (Indexed (J) (𝒰 𝑖 since isCategory:𝒰)) -> (Indexed (J) (𝒰 𝑖 since {!!}))
--     -- field PIErr : Functor (𝐈𝐱 (base b) (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 (base b) (𝐔𝐧𝐢𝐯 𝑖))


-}
-- 𝐈𝐧𝐟



