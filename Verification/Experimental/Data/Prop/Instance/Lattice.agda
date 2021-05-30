
module Verification.Experimental.Data.Prop.Instance.Lattice where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Data.Prop.Instance.Setoid
open import Verification.Experimental.Data.Prop.Instance.Preorder
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Instance.Preorder
open import Verification.Experimental.Data.Universe.Instance.Lattice
open import Verification.Experimental.Data.Sum.Definition

-- data ⊥-Prop {𝑖} : Prop 𝑖 where

instance
  hasFiniteJoins:Prop : hasFiniteJoins ′ Prop 𝑖 ′
  hasFiniteJoins.⊥         hasFiniteJoins:Prop = ∣ ⊥-𝒰 ∣
  hasFiniteJoins.initial-⊥ hasFiniteJoins:Prop = incl $ λ {()}
  hasFiniteJoins._∨_       hasFiniteJoins:Prop = λ A B -> ∣ ⟨ A ⟩ +-𝒰 ⟨ B ⟩ ∣
  hasFiniteJoins.ι₀-∨      hasFiniteJoins:Prop = incl left
  hasFiniteJoins.ι₁-∨      hasFiniteJoins:Prop = incl right
  hasFiniteJoins.[_,_]-∨   hasFiniteJoins:Prop f g = incl $ either ⟨ f ⟩ ⟨ g ⟩


instance
  hasFiniteMeets:Prop : hasFiniteMeets ′ Prop 𝑖 ′
  hasFiniteMeets.⊤          hasFiniteMeets:Prop = ∣ ⊤-𝒰 ∣
  hasFiniteMeets.terminal-⊤ hasFiniteMeets:Prop = incl (λ _ -> tt)
  hasFiniteMeets._∧_        hasFiniteMeets:Prop = λ a b -> ∣ ⟨ a ⟩ ×-𝒰 ⟨ b ⟩ ∣
  hasFiniteMeets.π₀-∧       hasFiniteMeets:Prop = incl fst
  hasFiniteMeets.π₁-∧       hasFiniteMeets:Prop = incl snd
  hasFiniteMeets.⟨_,_⟩-∧    hasFiniteMeets:Prop f g = incl (λ a -> ⟨ f ⟩ a , ⟨ g ⟩ a)


instance
  hasAllJoins:Prop : hasAllJoins 𝑖 ′ Prop 𝑖 ′
  hasAllJoins.⋁ hasAllJoins:Prop F = ∣ ∑ (λ a -> ⟨ F a ⟩) ∣
  hasAllJoins.ι-⋁ hasAllJoins:Prop = λ x → incl (λ Fx → x , Fx)
  hasAllJoins.[ hasAllJoins:Prop ]-⋁ = λ P → incl (λ (x , Px) → ⟨ P x ⟩ Px)

instance
  hasAllMeets:Prop : hasAllMeets 𝑖 ′ Prop 𝑖 ′
  hasAllMeets.⋀ hasAllMeets:Prop F = ∣ ∏ (λ a -> ⟨ F a ⟩) ∣
  hasAllMeets.π-⋀ hasAllMeets:Prop = λ x → incl (λ Fx → Fx x)
  hasAllMeets.⟨ hasAllMeets:Prop ⟩-⋀ = λ P → incl (λ F → λ x -> ⟨ P x ⟩ F)
