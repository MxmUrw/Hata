
module Verification.Experimental.Computation.Unification.RiFl.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Preservation


module _ (𝒞 : 𝒰 𝑖) {{_ : isCategory {𝑖₁} 𝒞}} where
  HomClass : ∀ 𝑗 -> 𝒰 _
  HomClass 𝑗 = ∀{a b : 𝒞} -> a ⟶ b -> 𝒰 𝑗


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑖₁} 𝒞}} where
  record Factorization (P : HomClass 𝒞 𝑗) (Q : HomClass 𝒞 𝑘) {a b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑖₁) where
    constructor factorization
    field center : 𝒞
    field fst : a ⟶ center
    field fstP : P fst
    field snd : center ⟶ b
    field sndP : Q snd
    field reduce-Factorization : fst ◆ snd ∼ f

module _ {𝒞 : Category 𝑖} {𝒳 : Category 𝑗} where
  record inImage (F : Functor 𝒞 𝒳) {a b : ⟨ 𝒳 ⟩} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
    field altdom : ⟨ 𝒳 ⟩
    field altcod : ⟨ 𝒳 ⟩
    field althom : altdom ⟶ altcod


record isRigidFlex (ℛ : Category 𝑗) (ℱ : Category 𝑘) {𝑖} (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺) ､ (𝑘 ⁺)) where
  field rigid : Functor ℛ 𝒞
  field flex : Functor ℱ 𝒞
  field factor-RiFl : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Factorization (inImage rigid) (inImage flex) f
  field split : ∀{a b : ⟨ ℛ ⟩} -> (f : a ⟶ b) -> Functor ℱ ℱ
  field split-over-rigid : ∀{a b : ⟨ ℛ ⟩} {f : a ⟶ b} -> ∀{a' : ⟨ ℱ ⟩} -> ⟨ flex ⟩ a' ≅ ⟨ rigid ⟩ a -> ⟨ flex ⟩ (⟨ split f ⟩ a') ≅ ⟨ rigid ⟩ b

open isRigidFlex {{...}} public

module _ {𝒞 : Category 𝑖} {ℛ : Category 𝑗} {ℱ : Category 𝑘} {{_ : isRigidFlex ℛ ℱ 𝒞}} where
  module _ {a b x : ⟨ ℱ ⟩} {f g : a ⟶ b} {{_ : isCoequalizer f g x}} where
    private
      π₌' : ⟨ flex ⟩ b ⟶ ⟨ flex ⟩ x
      π₌' = map π₌

      equate-π₌' : map f ◆ map π₌ ∼ map g ◆ map π₌
      equate-π₌' = equate-π₌
        ⟪ cong-∼ ⟫
        ⟪ functoriality-◆ ≀∼≀ functoriality-◆ ⟫

      compute-Coeq' : ∀{c : ⟨ 𝒞 ⟩} -> (h : ⟨ flex ⟩ b ⟶ c) -> (p : map f ◆ h ∼ map g ◆ h) -> ∑ λ (ξ : ⟨ flex ⟩ x ⟶ c) -> map π₌ ◆ ξ ∼ h
      compute-Coeq' h p =
        let factorization x h₀ h₀∈ℛ h₁ h₁∈ℱ reduce-h = factor-RiFl h
        in {!!}

  --   instance
  --     isCoequalizer:flex : isCoequalizer (map f) (map g) (⟨ flex ⟩ x)
  --     isCoequalizer.π₌ isCoequalizer:flex = π₌'
  --     isCoequalizer.equate-π₌ isCoequalizer:flex = equate-π₌'
  --     isCoequalizer.compute-Coeq isCoequalizer:flex = compute-Coeq'
  --     isCoequalizer.isEpi:π₌ isCoequalizer:flex = {!!}


  -- instance
  --   preservesCoequalizers:flex : preservesCoequalizers flex
  --   preservesCoequalizers:flex = {!!}



