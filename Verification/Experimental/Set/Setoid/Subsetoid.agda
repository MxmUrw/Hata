
module Verification.Experimental.Set.Setoid.Subsetoid where

open import Verification.Conventions

open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice

module _ {X : Setoid 𝑖} where

  instance
    isSetoid:Subsetoid : isSetoid _ (Subsetoid X)
    isSetoid:Subsetoid = isSetoid:hasU

  instance
    isPreorder:Subsetoid : isPreorder _ ′(Subsetoid X)′
    isPreorder._≤'_ isPreorder:Subsetoid a b = ⟨ a ⟩ ≤' ⟨ b ⟩
    isPreorder.reflexive isPreorder:Subsetoid = incl ⟨ reflexive ⟩
    isPreorder._⟡_ isPreorder:Subsetoid p q = incl ⟨ incl ⟨ p ⟩ ⟡ incl ⟨ q ⟩ ⟩
    isPreorder.transp-≤ isPreorder:Subsetoid p q P = incl ⟨ transp-≤ (incl ⟨ p ⟩) (incl ⟨ q ⟩) (incl ⟨ P ⟩) ⟩

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
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Subsetoid = incl ⟨ terminal-⊤ ⟩
    hasFiniteMeets._∧_ hasFiniteMeets:Subsetoid I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′
    hasFiniteMeets.π₀-∧ hasFiniteMeets:Subsetoid = incl ⟨ π₀-∧ ⟩
    hasFiniteMeets.π₁-∧ hasFiniteMeets:Subsetoid = incl ⟨ π₁-∧ ⟩
    hasFiniteMeets.⟨_,_⟩-∧ hasFiniteMeets:Subsetoid f g = incl ⟨ ⟨ (incl ⟨ f ⟩) , (incl ⟨ g ⟩) ⟩-∧ ⟩


