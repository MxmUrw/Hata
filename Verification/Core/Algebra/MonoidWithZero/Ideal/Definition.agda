
module Verification.Core.Algebra.MonoidWithZero.Ideal.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Subsetoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidAction.Definition


-- TODO: Give this a proper name, and move somewhere general
module _ {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) where
  ↓𝒫_ : A -> Prop 𝑗
  ↓𝒫_ a = ∣ P a ∣
-- end


record isIdeal {𝑗 : 𝔏 ^ 2} (A : Monoid₀ 𝑗) (P : 𝒫 ⟨ A ⟩ :& isSubsetoid) : 𝒰 𝑗 where
  field ideal-◍ : ◍ ∈ P
  field ideal-r-⋆ : ∀{a : ⟨ A ⟩} -> a ∈ P -> ∀ b -> (a ⋆ b) ∈ P
open isIdeal {{...}} public


module _ (A : 𝐌𝐨𝐧₀ 𝑗) where
  Idealᵘ : 𝒰 _
  Idealᵘ = _ :& isIdeal A

  macro Ideal = #structureOn Idealᵘ


module _ {A : Monoid₀ 𝑖} where

  private
    _∼-Ideal_ : Ideal A -> Ideal A -> 𝒰 _
    _∼-Ideal_ = _∼-hasU_

  instance
    isSetoid:Ideal : isSetoid (Ideal A)
    isSetoid:Ideal = isSetoid:hasU

  instance
    isPreorder:Ideal : isPreorder _ (Ideal A)
    isPreorder._≤_ isPreorder:Ideal I J = ⟨ I ⟩ ≤ ⟨ J ⟩
    isPreorder.reflexive isPreorder:Ideal = λ a → reflexive
    isPreorder._⟡_ isPreorder:Ideal = λ p q a → p a ⟡ q a
    isPreorder.transp-≤ isPreorder:Ideal = {!!}

  instance
    isPartialorder:Ideal : isPartialorder (Ideal A)
    isPartialorder:Ideal = record
      { antisym = λ p q -> incl $ antisym p q
      }



----------------------------------------------------------
-- A property of elements

module _ {A : 𝒰 _} {{_ : Monoid₀ 𝑖 on A}} where
  isZeroOrEpi : A -> 𝒰 _
  isZeroOrEpi a = (a ∼ ◍) +-𝒰 ((a ≁ ◍) ×-𝒰 ∀{b c : A} -> a ⋆ b ∼ a ⋆ c -> b ∼ c)

