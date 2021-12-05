
module Verification.Core.Space.Topological.Definition where

open import Verification.Conventions hiding (Discrete ; ∅ ; Bool ; _and_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice

module _ {A : 𝒰 𝑖} {𝒪 : 𝒰 𝑗} (Open : 𝒪 -> (A -> Prop 𝑖)) where
  record isGoodFamily (B : 𝒰 𝑖) (F : B -> 𝒪) : 𝒰 𝑖 where
    constructor goodFamily
    field noEmpties : ∀(b : B) -> ∑ λ a -> ⟨ Open (F b) a ⟩
    field decideBase : isDecidable B

  open isGoodFamily public

  GoodFamily : (B : 𝒰 𝑖) -> _
  GoodFamily B = (B -> 𝒪) :& isGoodFamily B

record isTopologicalᶜ (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺ ⁺) where
  constructor topological
  field 𝒪 : 𝒰 (𝑖 ⁺)
  field Open : 𝒪 -> (A -> Prop 𝑖)
  field ∅ : 𝒪
  field ℧ : 𝒪
  field _∩_ : 𝒪 -> 𝒪 -> 𝒪
  field ⋃ : ∀{B} -> (U : GoodFamily Open B) -> 𝒪
  field eval-∅ : Open ∅ ∼ ⊥
  field eval-℧ : Open ℧ ∼ ⊤
  field eval-∩ : ∀{u v : 𝒪} -> Open (u ∩ v) ∼ Open u ∧ Open v
  field eval-⋃ : ∀{B} {U : GoodFamily Open B} -> Open (⋃ U) ∼ ⋁ (Open ∘ ⟨ U ⟩)

  -- private
  --   None : ⊥-𝒰 -> 𝒪
  --   None = λ ()

  -- ∅ : 𝒪
  -- ∅ = ⋃ (None since goodFamily (λ ()) (left (λ ())))

  -- eval-∅ : Open ∅ ∼ ⊥
  -- eval-∅ = {!!} -- incl ({!!} , {!!})

open isTopologicalᶜ {{...}} public

Topologicalᶜ : ∀ 𝑖 -> 𝒰 _
Topologicalᶜ 𝑖 = 𝒰 𝑖 :& isTopologicalᶜ

𝐓𝐨𝐩ᶜ : ∀ 𝑖 -> SomeStructure
𝐓𝐨𝐩ᶜ 𝑖 = #structureOn (Topologicalᶜ 𝑖)




