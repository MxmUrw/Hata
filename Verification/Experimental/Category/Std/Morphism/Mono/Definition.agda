
module Verification.Experimental.Category.Std.Morphism.Mono.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Morphism
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Functor.Faithful
open import Verification.Experimental.Category.Std.Functor.Full
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Category.Notation.Associativity



module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record isMono {a b : 𝒞} (ϕ : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor mono
    field cancel-mono : ∀{x : 𝒞} -> ∀{α β : x ⟶ a} -> α ◆ ϕ ∼ β ◆ ϕ -> α ∼ β

  open isMono {{...}} public



--------------------------------------------------------------
-- Mono reflection


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isMonoReflecting (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field reflect-isMono : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{ϕ : a ⟶ b} -> isMono (map {{of F}} ϕ) -> isMono ϕ

  open isMonoReflecting {{...}} public


  -- Here we show that monos are reflected by faithful functors
  module _ {F : Functor 𝒞 𝒟} {{_ : isFaithful F}} where
    isMonoReflecting:byFaithful : isMonoReflecting F
    isMonoReflecting.reflect-isMono isMonoReflecting:byFaithful {a = a} {b} {ϕ} isMono:Fϕ = P
      where
        instance _ = isMono:Fϕ

        P : isMono ϕ
        isMono.cancel-mono P {z} {α} {β} x = Q
          where
            Q₀ : map α ◆ map ϕ ∼ map β ◆ map ϕ
            Q₀ = map α ◆ map ϕ    ⟨ functoriality-◆ ⁻¹ ⟩-∼
                 map (α ◆ ϕ)      ⟨ cong-∼ x ⟩-∼
                 map (β ◆ ϕ)      ⟨ functoriality-◆ ⟩-∼
                 map β ◆ map ϕ    ∎

            Q₁ : map α ∼ map β
            Q₁ = cancel-mono Q₀

            Q : α ∼ β
            Q = cancel-injective Q₁



--------------------------------------------------------------
-- Mono preservation

  record isMonoPreserving (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field preserve-isMono : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{ϕ : a ⟶ b} -> isMono ϕ -> isMono (map {{of F}} ϕ)

  open isMonoPreserving {{...}} public


  module _ {F : Functor 𝒞 𝒟} {{_ : hasSeparatingFamily 𝑘 𝒟}} {{_ : isFull F}} {{_ : isFaithful F}} where
    isMonoPreserving:byFullyFaithful : (∀ (s : Separator) -> inEssentialImage F (separator s)) -> isMonoPreserving F
    isMonoPreserving.preserve-isMono (isMonoPreserving:byFullyFaithful P) {a} {b} {f} isMono:f = Q
      where
        instance _ = isMono:f

        Q : isMono (map f)
        isMono.cancel-mono Q {z} {α} {β} α◆Ff∼β◆Ff = R
          where

            lem-10 : ∀ {s : Separator} -> ∀(σ : separator s ⟶ z) -> σ ◆ α ∼ σ ◆ β
            lem-10 {s} σ =
              let s' , Fs'≅s = P s
                  Fα' = ⟨ Fs'≅s ⟩ ◆ (σ ◆ α)
                  Fβ' = ⟨ Fs'≅s ⟩ ◆ (σ ◆ β)
                  α' = surj (Fα')
                  β' = surj (Fβ')

                  lem-10-1 : map (α' ◆ f) ∼ map (β' ◆ f)
                  lem-10-1 = map (α' ◆ f)                    ⟨ functoriality-◆ ⟩-∼
                             map α' ◆ map f                  ⟨ inv-surj ◈ refl ⟩-∼
                             ⟨ Fs'≅s ⟩ ◆ (σ ◆ α) ◆ map f     ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⁻¹ ⟩-∼
                             (⟨ Fs'≅s ⟩ ◆ σ) ◆ (α ◆ map f)   ⟨ refl ◈ α◆Ff∼β◆Ff ⟩-∼
                             (⟨ Fs'≅s ⟩ ◆ σ) ◆ (β ◆ map f)   ⟨ assoc-[ab][cd]∼a[bc]d-◆ ⟩-∼
                             ⟨ Fs'≅s ⟩ ◆ (σ ◆ β) ◆ map f     ⟨ inv-surj ⁻¹ ◈ refl ⟩-∼
                             map β' ◆ map f                  ⟨ functoriality-◆ ⁻¹ ⟩-∼
                             map (β' ◆ f)    ∎

                  lem-10-2 : α' ◆ f ∼ β' ◆ f
                  lem-10-2 = cancel-injective lem-10-1

                  lem-10-3 : α' ∼ β'
                  lem-10-3 = cancel-mono lem-10-2

                  lem-10-4 : map α' ∼ map β'
                  lem-10-4 = cong-∼ lem-10-3

                  lem-10-5 : Fα' ∼ Fβ'
                  lem-10-5 = Fα'              ⟨ inv-surj ⁻¹ ⟩-∼
                             map (surj Fα')   ⟨ lem-10-4 ⟩-∼
                             map (surj Fβ')   ⟨ inv-surj ⟩-∼
                             Fβ'              ∎

                  lem-10-6 : σ ◆ α ∼ σ ◆ β
                  lem-10-6 = σ ◆ α                                         ⟨ unit-l-◆ ⁻¹ ⟩-∼
                             id ◆ (σ ◆ α)                                  ⟨ inv-l-◆ (of Fs'≅s) ⁻¹ ◈ refl ⟩-∼
                             (inverse-◆ (of Fs'≅s) ◆ ⟨ Fs'≅s ⟩) ◆ (σ ◆ α)  ⟨ assoc-l-◆ ⟩-∼
                             inverse-◆ (of Fs'≅s) ◆ (⟨ Fs'≅s ⟩ ◆ (σ ◆ α))  ⟨ refl ◈ lem-10-5 ⟩-∼
                             inverse-◆ (of Fs'≅s) ◆ (⟨ Fs'≅s ⟩ ◆ (σ ◆ β))  ⟨ assoc-r-◆ ⟩-∼
                             (inverse-◆ (of Fs'≅s) ◆ ⟨ Fs'≅s ⟩) ◆ (σ ◆ β)  ⟨ inv-l-◆ (of Fs'≅s) ◈ refl ⟩-∼
                             id ◆ (σ ◆ β)                                  ⟨ unit-l-◆ ⟩-∼
                             σ ◆ β                                          ∎


              in lem-10-6

            R : α ∼ β
            R = separate α β lem-10


