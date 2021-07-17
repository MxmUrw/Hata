
module Verification.Experimental.Category.Std.Functor.Instance.Monoidal where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Iso
open import Verification.Experimental.Algebra.Monoid.Definition



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  private instance
    _ : isSetoid ⟨ 𝒟 ⟩
    _ = isSetoid:byCategory

  module _ {{_ : isMonoidal 𝒟}} where

    _⊗-𝐅𝐮𝐧𝐜_ : (F G : 𝐅𝐮𝐧𝐜 𝒞 𝒟) -> 𝐅𝐮𝐧𝐜 𝒞 𝒟
    _⊗-𝐅𝐮𝐧𝐜_ F G = H since lem-1
      where
        H = (λ x -> ⟨ F ⟩ x ⊗ ⟨ G ⟩ x)

        lem-1 : isFunctor 𝒞 𝒟 H
        isFunctor.map lem-1               = λ f → map (map f , map f)
        isFunctor.isSetoidHom:map lem-1   = record { cong-∼ = λ p → cong-∼ (cong-∼ p , cong-∼ p) }
        isFunctor.functoriality-id lem-1  =
          map (map id , map id)           ⟨ cong-∼ (functoriality-id , functoriality-id) ⟩-∼
          map (id , id)                   ⟨ functoriality-id ⟩-∼
          id {{of 𝒟}}                     ∎
        isFunctor.functoriality-◆ lem-1 {f = f} {g} =
          map (map (f ◆ g) , map (f ◆ g))           ⟨ cong-∼ (functoriality-◆ , functoriality-◆) ⟩-∼
          map (map f ◆ map g , map f ◆ map g)       ⟨ functoriality-◆ ⟩-∼
          map (map f , map f) ◆ map (map g , map g) ∎


    𝖨-𝐅𝐮𝐧𝐜 : 𝐅𝐮𝐧𝐜 𝒞 𝒟
    𝖨-𝐅𝐮𝐧𝐜 = const ◌ since lem-1
      where
        lem-1 : isFunctor 𝒞 𝒟 (const ◌)
        isFunctor.map lem-1              = λ f → id
        isFunctor.isSetoidHom:map lem-1  = record { cong-∼ = λ p → refl }
        isFunctor.functoriality-id lem-1 = refl
        isFunctor.functoriality-◆ lem-1  = unit-2-◆ ⁻¹

    private
      lem-1 : ∀{F : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> (𝖨-𝐅𝐮𝐧𝐜 ⊗-𝐅𝐮𝐧𝐜 F) ∼ F
      lem-1 {F} = α since lem-3
        where
          α : Natural (𝖨-𝐅𝐮𝐧𝐜 ⊗-𝐅𝐮𝐧𝐜 F) F
          α = ⟨ unit-l-⋆ ⟩ since natural (λ f → naturality {{naturalThere (isNaturalIso:unit-l-⋆)}} _)

          lem-3 = {!!}


    instance
      isMonoid:𝐅𝐮𝐧𝐜 : isMonoid (𝐅𝐮𝐧𝐜 𝒞 𝒟)
      isMonoid:𝐅𝐮𝐧𝐜 = record
                        { _⋆_        = _⊗-𝐅𝐮𝐧𝐜_
                        ; ◌          = 𝖨-𝐅𝐮𝐧𝐜
                        ; unit-l-⋆   = {!!}
                        ; unit-r-⋆   = {!!}
                        ; assoc-l-⋆  = {!!}
                        ; assoc-r-⋆  = {!!}
                        ; _`cong-⋆`_ = {!!}
                        }


