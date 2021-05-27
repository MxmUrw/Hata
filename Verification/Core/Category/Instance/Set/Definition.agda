

module Verification.Core.Category.Instance.Set.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Homotopy.Level
open import Verification.Core.Category.Instance.Type.Definition

-- [Hide]
private
  instance _ = isEquivRel:Path
-- //

-- | In order to define |Category:Set|, we need to say what a set is.
--   Since the notion of the homotopy level of a type is already defined,
--   we merely say:

-- [Definition]
-- | The type [..] of sets contains all types which have homotopy level 2, i.e., [..].
Set : (𝑖 : 𝔏) -> 𝒰 (𝑖 ⁺)
Set 𝑖 = HType 2 𝑖
-- //

-- | This allows us to define the category of sets:

-- [Example]
-- | The category of sets [..] is given by:
Category:Set : (𝑖 : 𝔏) -> Category (𝑖 ⁺ , 𝑖 , 𝑖)

-- | - The underlying type is [..].
⟨ Category:Set 𝑖 ⟩ = Set 𝑖

-- | - Arrows between two sets |A| and |B| are simply functions |A → B|.
--     But for better type inference we wrap them in a newtype, [..].
isCategory.Hom (of Category:Set 𝑖) A B = HTypeHom A B

-- | - Equality of arrows is given by equality of the underlying functions:
isCategory._≣_ (of Category:Set 𝑖) f g = ∀ x -> ⟨ f ⟩ x ≡ ⟨ g ⟩ x

-- |>  As this is the usual path type, it is an equivalence relation:
isEquivRel.refl  (isCategory.isEquivRel:≣ (of Category:Set 𝑖)) = λ x -> refl
isEquivRel.sym   (isCategory.isEquivRel:≣ (of Category:Set 𝑖)) p = λ x -> sym (p x)
isEquivRel._∙_   (isCategory.isEquivRel:≣ (of Category:Set 𝑖)) p q = λ x -> p x ∙ q x

-- | - Identity and composition are inherited from |Category:𝒰|
isCategory.id   (of Category:Set 𝑖) = ` id-𝒰 `
isCategory._◆_  (of Category:Set 𝑖) f g = ` comp-𝒰 ⟨ f ⟩ ⟨ g ⟩ `

-- | - All equations hold trivially as well.
isCategory.unit-l-◆    (of Category:Set 𝑖) x = refl
isCategory.unit-r-◆    (of Category:Set 𝑖) x = refl
isCategory.unit-2-◆    (of Category:Set 𝑖) x = refl
isCategory.assoc-l-◆   (of Category:Set 𝑖) x = refl
isCategory.assoc-r-◆   (of Category:Set 𝑖) x = refl
isCategory._◈_         (of Category:Set 𝑖) p q x = λ i -> (q (p x i) i)
-- //


instance isCategory:Set = #openstruct Category:Set






