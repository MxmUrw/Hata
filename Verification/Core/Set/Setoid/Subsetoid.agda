
module Verification.Core.Set.Setoid.Subsetoid where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice

module _ {X : Setoid 𝑖} where

  instance
    isSetoid:Subsetoid : isSetoid (Subsetoid X)
    isSetoid:Subsetoid = isSetoid:hasU

  instance
    isPreorder:Subsetoid : isPreorder _ ′(Subsetoid X)′
    isPreorder._≤_ isPreorder:Subsetoid = ≤-Base (λ a b -> ⟨ a ⟩ ≤ ⟨ b ⟩)
    isPreorder.reflexive isPreorder:Subsetoid = incl reflexive
    isPreorder._⟡_ isPreorder:Subsetoid p q = incl (⟨ p ⟩ ⟡ ⟨ q ⟩)
    isPreorder.transp-≤ isPreorder:Subsetoid p q P = {!!} -- incl (⟨ transp-≤ ⟨ p ⟩ ⟨ q ⟩ (incl ⟨ P ⟩) ⟩)
    -- incl ⟨ transp-≤ (incl ⟨ p ⟩) (incl ⟨ q ⟩) (incl ⟨ P ⟩) ⟩

  instance
    isSubsetoid:⊤ : isSubsetoid {X = ⟨ X ⟩} ⊤
    isSubsetoid.transp-Subsetoid isSubsetoid:⊤ p _ = tt

    -- isSubsetoid:∧ : ∀{U V : Subsetoid X} -> isSubsetoid X (⟨ U ⟩ ∧ ⟨ V ⟩)

    isSubsetoid:∧ : ∀{U V : 𝒫 ⟨ X ⟩} {{_ : isSubsetoid U}} {{_ : isSubsetoid V}} -> isSubsetoid (U ∧ V)
    isSubsetoid:∧ = record
      { transp-Subsetoid = λ p (P , Q) -> transp-Subsetoid p P , transp-Subsetoid p Q
      }

  instance
    hasFiniteMeets:Subsetoid : hasFiniteMeets ′(Subsetoid X)′
    hasFiniteMeets.⊤ hasFiniteMeets:Subsetoid = ′ ⊤ ′
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Subsetoid = incl terminal-⊤
    hasFiniteMeets._∧_ hasFiniteMeets:Subsetoid I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′
    hasFiniteMeets.π₀-∧ hasFiniteMeets:Subsetoid = incl π₀-∧
    hasFiniteMeets.π₁-∧ hasFiniteMeets:Subsetoid = incl π₁-∧
    hasFiniteMeets.⟨_,_⟩-∧ hasFiniteMeets:Subsetoid f g = {!!}

  instance
    isSubsetoid:⊥ : isSubsetoid {X = ⟨ X ⟩} ⊥
    isSubsetoid.transp-Subsetoid isSubsetoid:⊥ p _ = {!!}


    isSubsetoid:∨ : ∀{U V : 𝒫 ⟨ X ⟩} {{_ : isSubsetoid U}} {{_ : isSubsetoid V}} -> isSubsetoid (U ∨ V)
    isSubsetoid:∨ = {!!} -- record
      -- { transp-Subsetoid = λ p (P , Q) -> transp-Subsetoid p P , transp-Subsetoid p Q
      -- }

  instance
    hasFiniteJoins:Subsetoid : hasFiniteJoins ′(Subsetoid X)′
    hasFiniteJoins.⊥ hasFiniteJoins:Subsetoid = ′ ⊥ ′
    hasFiniteJoins.initial-⊥ hasFiniteJoins:Subsetoid = incl initial-⊥
    hasFiniteJoins._∨_ hasFiniteJoins:Subsetoid I J = ′ ⟨ I ⟩ ∨ ⟨ J ⟩ ′
    hasFiniteJoins.ι₀-∨ hasFiniteJoins:Subsetoid = incl ι₀-∨
    hasFiniteJoins.ι₁-∨ hasFiniteJoins:Subsetoid = incl ι₁-∨
    hasFiniteJoins.[_,_]-∨ hasFiniteJoins:Subsetoid f g = {!!}
      -- incl ⟨ ⟨ (incl ⟨ f ⟩) , (incl ⟨ g ⟩) ⟩-∧ ⟩


