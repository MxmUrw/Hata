
module Verification.Experimental.Category.Std.Monad.KleisliCategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Definition


record Kleisli {𝒞 : Category 𝑖} (T : Monad 𝒞) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : ⟨ 𝒞 ⟩
open Kleisli {{...}} public


module _ {𝒞 : Category 𝑖} {T : Monad 𝒞} where


  KleisliHom : (A B : Kleisli T) -> 𝒰 _
  KleisliHom = Hom-Base (λ x y -> ⟨ x ⟩ ⟶ ⟨ T ⟩ ⟨ y ⟩)

  module _ {A B : Kleisli T} where
    _∼-KleisliHom_ : (f g : KleisliHom A B) -> 𝒰 _
    _∼-KleisliHom_ f g = ⟨ f ⟩ ∼ ⟨ g ⟩

    instance
      isEquivRel:∼-KleisliHom : isEquivRel (∼-Base (_∼-KleisliHom_))
      isEquivRel:∼-KleisliHom = {!!}

    instance
      isSetoid:KleisliHom : isSetoid _ (KleisliHom A B)
      isSetoid._∼'_ isSetoid:KleisliHom = _∼-KleisliHom_
      isSetoid.isEquivRel:∼ isSetoid:KleisliHom = isEquivRel:∼-KleisliHom


  instance
    Category:Kleisli : isCategory _ (Kleisli T)
    isCategory.Hom' Category:Kleisli A B = ⟨ A ⟩ ⟶ ⟨ T ⟩ ⟨ B ⟩
    isCategory.isSetoid:Hom Category:Kleisli = it
    isCategory.id Category:Kleisli = incl pure
    isCategory._◆_ Category:Kleisli = {!!}
    isCategory.unit-l-◆ Category:Kleisli = {!!}
    isCategory.unit-r-◆ Category:Kleisli = {!!}
    isCategory.unit-2-◆ Category:Kleisli = {!!}
    isCategory.assoc-l-◆ Category:Kleisli = {!!}
    isCategory.assoc-r-◆ Category:Kleisli = {!!}
    isCategory._◈_ Category:Kleisli = {!!}





