
module Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.RelativeMonad.Definition

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  module _ {J : Functor 𝒞 𝒟}  where
    record RelativeKleisli (T : RelativeMonad J) : 𝒰 𝑖 where
      constructor incl
      field ⟨_⟩ : ⟨ 𝒞 ⟩
    open RelativeKleisli {{...}} public

    macro
      𝐑𝐞𝐊𝐥𝐬 : (T : RelativeMonad J) -> SomeStructure
      𝐑𝐞𝐊𝐥𝐬 T = #structureOn (RelativeKleisli T)

  module _ {J : Functor 𝒞 𝒟} {T : RelativeMonad J} where

    RelativeKleisliHom : (A B : 𝐑𝐞𝐊𝐥𝐬 T) -> 𝒰 _
    RelativeKleisliHom = Hom-Base (λ x y -> ⟨ J ⟩ ⟨ x ⟩ ⟶ ⟨ T ⟩ ⟨ y ⟩)

    module _ {A B : 𝐑𝐞𝐊𝐥𝐬 T} where
      _∼-RelativeKleisliHom_ : (f g : RelativeKleisliHom A B) -> 𝒰 _
      _∼-RelativeKleisliHom_ = ∼-Base (λ f g -> ⟨ f ⟩ ∼ ⟨ g ⟩)

      instance
        isSetoid:RelativeKleisliHom : isSetoid (RelativeKleisliHom A B)
        isSetoid._∼_ isSetoid:RelativeKleisliHom = _∼-RelativeKleisliHom_
        isSetoid.refl isSetoid:RelativeKleisliHom {a} = incl refl
        isSetoid.sym isSetoid:RelativeKleisliHom {a} {b} p = incl (sym ⟨ p ⟩)
        isSetoid._∙_ isSetoid:RelativeKleisliHom {a} p q = incl $ ⟨ p ⟩ ∙ ⟨ q ⟩

    id-𝐑𝐞𝐊𝐥𝐬 : ∀{a : 𝐑𝐞𝐊𝐥𝐬 T} -> RelativeKleisliHom a a
    id-𝐑𝐞𝐊𝐥𝐬 = incl repure

    infixl 50 _◆-𝐑𝐞𝐊𝐥𝐬_
    _◆-𝐑𝐞𝐊𝐥𝐬_ : ∀{a b c : 𝐑𝐞𝐊𝐥𝐬 T} -> (RelativeKleisliHom a b) -> (RelativeKleisliHom b c) -> RelativeKleisliHom a c
    _◆-𝐑𝐞𝐊𝐥𝐬_ f g = incl (⟨ f ⟩ ◆ reext ⟨ g ⟩)

    private
      lem-1 : ∀{a b : 𝐑𝐞𝐊𝐥𝐬 T} -> {f : RelativeKleisliHom a b} -> id-𝐑𝐞𝐊𝐥𝐬 ◆-𝐑𝐞𝐊𝐥𝐬 f ∼ f
      lem-1 = incl reunit-l

      lem-2 : ∀{a b : 𝐑𝐞𝐊𝐥𝐬 T} -> {f : RelativeKleisliHom a b} -> f ◆-𝐑𝐞𝐊𝐥𝐬 id-𝐑𝐞𝐊𝐥𝐬 ∼ f
      lem-2 = incl ((refl ◈ reunit-r) ∙ unit-r-◆)

      lem-3 : ∀{a b c d : 𝐑𝐞𝐊𝐥𝐬 T} {f : RelativeKleisliHom a b} {g : RelativeKleisliHom b c} {h : RelativeKleisliHom c d}
              -> (f ◆-𝐑𝐞𝐊𝐥𝐬 g) ◆-𝐑𝐞𝐊𝐥𝐬 h ∼ f ◆-𝐑𝐞𝐊𝐥𝐬 (g ◆-𝐑𝐞𝐊𝐥𝐬 h)
      lem-3 {f = incl f} {incl g} {incl h} = incl P
        where
          P : (f ◆ reext g) ◆ reext h ∼ f ◆ (reext (g ◆ reext h))
          P = (f ◆ reext g) ◆ reext h   ⟨ assoc-l-◆ ⟩-∼
              f ◆ (reext g ◆ reext h)   ⟨ refl ◈ reassoc ⟩-∼
              f ◆ (reext (g ◆ reext h)) ∎

    instance
      Category:RelativeKleisli : isCategory (RelativeKleisli T)
      isCategory.Hom Category:RelativeKleisli A B = RelativeKleisliHom A B
      isCategory.isSetoid:Hom Category:RelativeKleisli = it
      isCategory.id Category:RelativeKleisli         = incl repure
      isCategory._◆_ Category:RelativeKleisli        = _◆-𝐑𝐞𝐊𝐥𝐬_
      isCategory.unit-l-◆ Category:RelativeKleisli   = lem-1
      isCategory.unit-r-◆ Category:RelativeKleisli   = lem-2
      isCategory.unit-2-◆ Category:RelativeKleisli   = lem-1
      isCategory.assoc-l-◆ Category:RelativeKleisli  = lem-3
      isCategory.assoc-r-◆ Category:RelativeKleisli  = (lem-3 ⁻¹)
      isCategory._◈_ Category:RelativeKleisli        = {!!} -- λ p q -> incl $ lem-4 ⟨ p ⟩ ⟨ q ⟩



