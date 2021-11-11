
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Set.Setoid.Morphism


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F : Functor 𝒞 𝒟} {{_ : isFull F}} {{_ : isFaithful F}} where

  module _ {a b x : ⟨ 𝒞 ⟩} (P : isCoproduct (⟨ F ⟩ a) (⟨ F ⟩ b) (⟨ F ⟩ x)) where
    private
      instance _ = P
      ι₀' : a ⟶ x
      ι₀' = surj ι₀

      ι₁' : b ⟶ x
      ι₁' = surj ι₁

      ⦗_⦘' : ∀{y} -> (a ⟶ y) × (b ⟶ y) -> x ⟶ y
      ⦗_⦘' (f , g) = surj (⦗ map f , map g ⦘)

    isCoproduct:byFullyFaithfull : isCoproduct a b x
    isCoproduct.ι₀ isCoproduct:byFullyFaithfull = ι₀'
    isCoproduct.ι₁ isCoproduct:byFullyFaithfull = ι₁'
    isCoproduct.⦗ isCoproduct:byFullyFaithfull ⦘ = ⦗_⦘'
    isCoproduct.isSetoidHom:⦗⦘ isCoproduct:byFullyFaithfull = {!!}
    isCoproduct.reduce-ι₀ isCoproduct:byFullyFaithfull = {!!}
    isCoproduct.reduce-ι₁ isCoproduct:byFullyFaithfull = {!!}
    isCoproduct.expand-ι₀,ι₁ isCoproduct:byFullyFaithfull = {!!}

  module _ {{_ : isEssentiallySurjective F}} {{_ : hasCoproducts 𝒟}} where
    private
      _⊔'_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
      _⊔'_ a b = eso (⟨ F ⟩ a ⊔ ⟨ F ⟩ b)

      module _ {a b : ⟨ 𝒞 ⟩} where
        lem-10 : isCoproduct a b (a ⊔' b)
        lem-10 = isCoproduct:byFullyFaithfull (transp-≅-Coproduct p)
          where
            p : (⟨ F ⟩ a ⊔ ⟨ F ⟩ b) ≅ ⟨ F ⟩ (eso (⟨ F ⟩ a ⊔ ⟨ F ⟩ b))
            p = sym-≅ inv-eso

      lem-20 : hasCoproducts 𝒞
      hasCoproducts._⊔_ lem-20 = _⊔'_
      hasCoproducts.isCoproduct:⊔ lem-20 = lem-10

    hasCoproducts:byFFEso : hasCoproducts 𝒞
    hasCoproducts:byFFEso = lem-20


  module _ {{_ : isEssentiallySurjective F}} {{_ : hasInitial 𝒟}} where
    private
      ⊥' : ⟨ 𝒞 ⟩
      ⊥' = eso ⊥

      instance
        isInitial:byFFEso : isInitial ⊥'
        isInitial:byFFEso = {!!}

    hasInitial:byFFEso : hasInitial 𝒞
    hasInitial.⊥ hasInitial:byFFEso = ⊥'
    hasInitial.isInitial:⊥ hasInitial:byFFEso = it

  module _ {{_ : isEssentiallySurjective F}} {{_ : hasFiniteCoproducts 𝒟}} where
    hasFiniteCoproducts:byFFEso : hasFiniteCoproducts 𝒞
    hasFiniteCoproducts.hasInitial:this hasFiniteCoproducts:byFFEso = hasInitial:byFFEso
    hasFiniteCoproducts.hasCoproducts:this hasFiniteCoproducts:byFFEso = hasCoproducts:byFFEso



    -- isCoproduct:byFullSubcategory : {{_ : isCoproduct (f ⟨ a ⟩) (f ⟨ b ⟩) (f ⟨ x ⟩)}} -> isCoproduct a b x
    -- isCoproduct.ι₀ isCoproduct:byFullSubcategory = incl ι₀
    -- isCoproduct.ι₁ isCoproduct:byFullSubcategory = incl ι₁
    -- isCoproduct.⦗ isCoproduct:byFullSubcategory ⦘ = λ (f , g) -> incl ⦗ ⟨ f ⟩ , ⟨ g ⟩ ⦘
    -- isCoproduct.isSetoidHom:⦗⦘ isCoproduct:byFullSubcategory = {!!}
    -- isCoproduct.reduce-ι₀ isCoproduct:byFullSubcategory = reduce-ι₀
    -- isCoproduct.reduce-ι₁ isCoproduct:byFullSubcategory = reduce-ι₁
    -- isCoproduct.expand-ι₀,ι₁ isCoproduct:byFullSubcategory = expand-ι₀,ι₁
