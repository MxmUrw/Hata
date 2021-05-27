

module Verification.Core.Category.Instance.Functor where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat.Definition
-- open import Verification.Core.Category.Instance.Type
-- open import Verification.Core.Category.Quiver
-- open import Verification.Core.Category.FreeCategory
-- open import Verification.Core.Category.Iso
-- open import Verification.Core.Category.Adjunction
-- open import Verification.Core.Category.Proper

-- [Example]
-- | Next, we look at functors and natural transformations. For this, let [..] and [..] be two categories.
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  -- | - On any functor [..],
  module _ (F : Functor 𝒞 𝒟) where

    -- |>  there is an identity natural transformation [..],
    Natural:id : Natural F F
    -- |> which returns the identity arrow in every component.
    ⟨ Natural:id ⟩ {x} = id
    -- | Naturality can be shown using unitality of |id| in |𝒟|.
    INatural.naturality (of Natural:id) f = unit-l-◆ ∙ sym unit-r-◆

  -- | - Given three functors [..],
  module _ {F G H : Functor 𝒞 𝒟} where
    -- |> we can compose natural transformations going between them as follows:
    Natural:comp : (α : Natural F G) -> (β : Natural G H) -> Natural F H
    ⟨ Natural:comp α β ⟩ {x} = ⟨ α ⟩ ◆ ⟨ β ⟩

    -- | Naturality derives from naturality of |α| and |β|.
    INatural.naturality (of Natural:comp α β) f =
      let P : ⟨ α ⟩ ◆ ⟨ β ⟩ ◆ map f ≣ map f ◆ (⟨ α ⟩ ◆ ⟨ β ⟩)
          P = assoc-l-◆ ∙ (refl ◈ (naturality f)) ∙ assoc-r-◆ ∙ (naturality f ◈ refl) ∙ assoc-l-◆
      in P

-- |: This means that for any pair of categories [..] and [..],
module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  -- |> we define [..] to have:
  Category:Functor : Category _

  -- | - Functors as objects
  ⟨ Category:Functor ⟩ = Functor 𝒞 𝒟

  -- | - Natural transformations between them as morphisms.
  isCategory.Hom (of Category:Functor) = Natural

  -- | - Identities and composition are given by the just defined |Natural:id| and |Natural:comp|.
  isCategory.id (of Category:Functor) = Natural:id _
  isCategory._◆_ (of Category:Functor) = Natural:comp
-- //
-- [Hide]
  isCategory._≣_ (of Category:Functor) = λ α β -> ∀ x -> ⟨ α ⟩ {x = x} ≣ ⟨ β ⟩
  isEquivRel.refl (isCategory.isEquivRel:≣ (of Category:Functor)) x = refl
  isEquivRel.sym (isCategory.isEquivRel:≣ (of Category:Functor)) p x = sym (p x)
  isEquivRel._∙_ (isCategory.isEquivRel:≣ (of Category:Functor)) p q x = p x ∙ q x
  isCategory.unit-l-◆ (of Category:Functor) x = unit-l-◆
  isCategory.unit-r-◆ (of Category:Functor) x = unit-r-◆
  isCategory.unit-2-◆ (of Category:Functor) x = unit-2-◆
  isCategory.assoc-l-◆ (of Category:Functor) x = assoc-l-◆
  isCategory.assoc-r-◆ (of Category:Functor) x = assoc-r-◆
  isCategory._◈_ (of Category:Functor) p q x = p x ◈ q x
-- //

instance isCategory:Functor = #openstruct Category:Functor

-- [Hide]
private
  _◇_ = comp-Cat

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {𝒢 : Category 𝑘} where
  module _ {a b : Functor 𝒞 𝒟} {c d : Functor 𝒟 𝒢} where
    _◆-H_ : (α : Natural a b) -> (β : Natural c d) -> Natural (a ◇ c) (b ◇ d)
    ⟨ α ◆-H β ⟩ {x} = ⟨ β ⟩ {⟨ a ⟩ x} ◆ map ⟨ α ⟩
    INatural.naturality (of (α ◆-H β)) f =
        let P : ⟨ β ⟩ ◆ map ⟨ α ⟩ ◆ map {{of (b ◇ d)}} f ≣ map {{of (a ◇ c)}} f ◆ (⟨ β ⟩ ◆ map ⟨ α ⟩)
            P = assoc-l-◆ ∙ (refl ◈ sym functoriality-◆)
                          ∙ (refl ◈ functoriality-≣ (naturality f))
                          ∙ (refl ◈ functoriality-◆)
                          ∙ assoc-r-◆
                          ∙ (naturality (map f) ◈ refl)
                          ∙ assoc-l-◆
        in P

  module _  {c d : Functor 𝒟 𝒢} where
    [_]◆-H_ : (a : Functor 𝒞 𝒟) -> (β : Natural c d) -> Natural (a ◇ c) (a ◇ d)
    ⟨ [ a ]◆-H β ⟩ {x} = ⟨ β ⟩ {⟨ a ⟩ x}
    INatural.naturality (of ([ a ]◆-H β)) f = naturality (map f)
-- //
