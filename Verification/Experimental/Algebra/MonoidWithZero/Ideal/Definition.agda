
module Verification.Experimental.Algebra.MonoidWithZero.Ideal.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition


-- TODO: Give this a proper name, and move somewhere general
module _ {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) where
  ↓𝒫_ : A -> Prop 𝑗
  ↓𝒫_ a = ∣ P a ∣
-- end


record isIdealᵣ {𝑗 : 𝔏 ^ 2} (A : Monoid₀ 𝑗) (P : 𝒫 ⟨ A ⟩ :& isSubsetoid) : 𝒰 𝑗 where
  field ideal-◍ : ◍ ∈ P
  field ideal-r-⋆ : ∀{a : ⟨ A ⟩} -> a ∈ P -> ∀ b -> (a ⋆ b) ∈ P
open isIdealᵣ {{...}} public


module _ (A : 𝐌𝐨𝐧₀ 𝑗) where
  Idealᵣᵘ : 𝒰 _
  Idealᵣᵘ = _ :& isIdealᵣ A

  macro Idealᵣ = #structureOn Idealᵣᵘ


module _ {A : Monoid₀ 𝑖} where

  private
    _∼-Ideal_ : Idealᵣ A -> Idealᵣ A -> 𝒰 _
    _∼-Ideal_ = _∼-hasU_

  instance
    isSetoid:Idealᵣ : isSetoid (Idealᵣ A)
    isSetoid:Idealᵣ = isSetoid:hasU

  instance
    isPreorder:Idealᵣ : isPreorder _ (Idealᵣ A)
    isPreorder._≤_ isPreorder:Idealᵣ I J = ⟨ I ⟩ ≤ ⟨ J ⟩
    isPreorder.reflexive isPreorder:Idealᵣ = λ a → reflexive
    isPreorder._⟡_ isPreorder:Idealᵣ = λ p q a → p a ⟡ q a
    isPreorder.transp-≤ isPreorder:Idealᵣ = {!!}

  instance
    isPartialorder:Idealᵣ : isPartialorder (Idealᵣ A)
    isPartialorder:Idealᵣ = record
      { antisym = λ p q -> incl $ antisym p q
      }



----------------------------------------------------------
-- A property of elements

module _ {A : 𝒰 _} {{_ : Monoid₀ 𝑖 on A}} where
  isZeroOrEpi : A -> 𝒰 _
  isZeroOrEpi a = (a ∼ ◍) +-𝒰 ((a ≁ ◍) ×-𝒰 ∀{b c : A} -> a ⋆ b ∼ a ⋆ c -> b ∼ c)

