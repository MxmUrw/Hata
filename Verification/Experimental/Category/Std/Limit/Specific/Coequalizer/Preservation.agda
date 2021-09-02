
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Preservation where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
-- open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Faithful
open import Verification.Experimental.Category.Std.Functor.Full
open import Verification.Experimental.Category.Std.Functor.EssentiallySurjective

open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record preservesCoequalizer (F : Functor 𝒞 𝒟) {a b : ⟨ 𝒞 ⟩} (f g : a ⟶ b) (x : ⟨ 𝒞 ⟩) {{_ : isCoequalizer f g x}} : 𝒰 (𝑖 ､ 𝑗) where
    field {{isCoequalizer:Image}} : isCoequalizer (map f) (map g) (⟨ F ⟩ x)
    field preserve-π₌ : map {{of F}} π₌ ∼ π₌

  open preservesCoequalizer {{...}} public

  -- record preservesInitial (F : Functor 𝒞 𝒟) (a : ⟨ 𝒞 ⟩) {{_ : isInitial a}} : 𝒰 (𝑖 ､ 𝑗) where
  --   field {{preserve-Initial}} : isInitial (⟨ F ⟩ a)

  -- module _ {{_ : hasFiniteCoproducts 𝒞}} where
  record preservesCoequalizers (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field {{preservesCoequalizers:this}} : ∀{a b x : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> {{_ : isCoequalizer f g x}} -> preservesCoequalizer F f g x

  --   open isFiniteCoproductPreserving {{...}} public

  --   module _ {F : Functor 𝒞 𝒟} {{_ : isFiniteCoproductPreserving F}} {{_ : hasFiniteCoproducts 𝒟}} where
  --     preserves-⊔ : ∀{a b : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ (a ⊔ b) ≅ ⟨ F ⟩ a ⊔ ⟨ F ⟩ b
  --     preserves-⊔ = {!!}


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F : Functor 𝒞 𝒟} {{_ : isFull F}} {{_ : isFaithful F}} {{_ : isEssentiallySurjective F}} where

  module _ {a b x : ⟨ 𝒞 ⟩} {f g : a ⟶ b} (P : isCoequalizer (f) (g) (x)) where
    private
      instance _ = P
      π₌' : ⟨ F ⟩ b ⟶ ⟨ F ⟩ x
      π₌' = map π₌

    isCoequalizer:byEquivalence : isCoequalizer (map f) (map g) (⟨ F ⟩ x)
    isCoequalizer.π₌ isCoequalizer:byEquivalence = π₌'
    isCoequalizer.equate-π₌ isCoequalizer:byEquivalence = {!!}
    isCoequalizer.compute-Coeq isCoequalizer:byEquivalence = {!!}
    isCoequalizer.isEpi:π₌ isCoequalizer:byEquivalence = {!!}


