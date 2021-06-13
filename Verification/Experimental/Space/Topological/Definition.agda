
module Verification.Experimental.Space.Topological.Definition where

open import Verification.Conventions hiding (Discrete ; ∅ ; Bool ; _and_)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice

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


module _ {𝑖 : 𝔏} where
  data Bool : 𝒰 𝑖 where
    false true : Bool

  macro 𝔹 = #structureOn Bool

_and_ : ∀{𝑖} -> 𝔹 {𝑖} -> 𝔹 {𝑖} -> 𝔹 {𝑖}
false and b = false
true and b = b


--------------------------------------------------------------------------------
-- Discrete topology on a type

record Discrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : A

open Discrete public

macro
  𝖣𝗂𝗌𝖼 : ∀(A : 𝒰 𝑖) -> SomeStructure
  𝖣𝗂𝗌𝖼 A = #structureOn (Discrete A)

instance
  isTopologicalᶜ:DiscreteTopological : ∀{A : 𝒰 𝑖} -> isTopologicalᶜ (𝖣𝗂𝗌𝖼 A)
  isTopologicalᶜ:DiscreteTopological {𝑖} {A = A} = topological 𝒪' Open' ⊥ ⊤ (_∧_) (λ F -> ⋁ ⟨ F ⟩) refl refl refl refl
    where 𝒪' = (A -> Prop 𝑖)
          Open' = λ u a -> u ⟨ a ⟩

--------------------------------------------------------------------------------
-- Codiscrete topology on a type

record Codiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : A

open Codiscrete public

macro
  𝖢𝗈𝖣𝗂𝗌𝖼 : ∀(A : 𝒰 𝑖) -> SomeStructure
  𝖢𝗈𝖣𝗂𝗌𝖼 A = #structureOn (Codiscrete A)



instance
  isTopologicalᶜ:CodiscreteTopological : ∀{A : 𝒰 𝑖} -> isTopologicalᶜ (𝖢𝗈𝖣𝗂𝗌𝖼 A)
  isTopologicalᶜ:CodiscreteTopological {𝑖} {A = A} = topological 𝒪' Open' (false) (true) (_and_) union refl refl (λ {u} {v} -> lem-1 {u} {v}) (λ {B} {U} -> lem-2 {B} {U})
    where 𝒪' = Bool
          Open' : 𝔹 -> _
          Open' (true) = ⊤
          Open' (false) = ⊥

          union : {B : 𝒰 𝑖} → GoodFamily Open' B → 𝒪'
          union F with decideBase (of F)
          ... | left x = false
          ... | just x = true

          lem-1 : {u v : 𝒪'} → Open' (u and v) ∼ Open' u ∧ Open' v
          lem-1 {false} {v} = absorb-l-∧ ⁻¹
          lem-1 {true} {v} = unit-l-∧ ⁻¹

          lem-2 : {B : 𝒰 𝑖} {U : GoodFamily Open' B} →
                  Open' (union U) ∼ (⋁ (Open' ∘ ⟨ U ⟩))
          lem-2 {B} {U} with decideBase (of U)
          ... | left x = empty-⋁ x ⁻¹
          ... | just b =
                   ⊤                       ⟨ absorb-r-∨ ⁻¹ ⟩-∼
                   (⋁ (Open' ∘ ⟨ U ⟩)) ∨ ⊤ ⟨ duplicate-r-⋁ b P ⟩-∼
                   (⋁ (Open' ∘ ⟨ U ⟩))      ∎
                where P : Open' (⟨ U ⟩ b) ∼ ⊤
                      P with  ⟨ U ⟩ b | noEmpties (of U) b
                      ... | true | Y = refl


