
module Verification.Core.Space.Topological.Specific.Discrete where

open import Verification.Conventions hiding (Discrete ; ∅ ; Bool ; _and_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice

open import Verification.Core.Space.Topological.Definition



module _ {𝑖 : 𝔏} where
  data Bool : 𝒰 𝑖 where
    false true : Bool

  macro 𝔹 = #structureOn Bool

_and_ : ∀{𝑖} -> 𝔹 {𝑖} -> 𝔹 {𝑖} -> 𝔹 {𝑖}
false and b = false
true and b = b


--------------------------------------------------------------------------------
-- Discrete topology on a type

{-
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

-}

--------------------------------------------------------------------------------
-- Codiscrete topology on a type

record Codiscrete (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : A

open Codiscrete public

macro
  𝖢𝗈𝖣𝗂𝗌𝖼 : ∀(A : 𝒰 𝑖) -> SomeStructure
  𝖢𝗈𝖣𝗂𝗌𝖼 A = #structureOn (Codiscrete A)


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  ∃₀ : (A -> B -> Prop 𝑘) -> B -> Prop (𝑖 ､ 𝑘)
  ∃₀ R b = ∣ ∑ (λ a → ⟨ R a b ⟩) ∣



instance
  isTopologicalᶜ:CodiscreteTopological : ∀{A : 𝒰 𝑖} -> isTopologicalᶜ (𝖢𝗈𝖣𝗂𝗌𝖼 A)
  isTopologicalᶜ:CodiscreteTopological {𝑖} {A = A} = topological 𝔹 Open' lem-1 {!!}
    where Open' : 𝔹 -> _
          Open' (true) = ⊤
          Open' (false) = ⊥

          lem-1 : ∃₀ Open' ∼ ⊤
          lem-1 = antisym terminal-⊤ (incl (λ x → true , tt))

          lem-2 : ∀{a b : 𝔹} -> Open' a ∧ Open' b ∼ ⋁ (λ (x : ⦋ a ↓[ Open' ] b ⦌) -> Open' ⟨ x ⟩)
          lem-2 {false} {b} = ⊥ ∧ Open' b    ⟨ absorb-l-∧ ⟩-∼
                              ⊥              ⟨ antisym initial-⊥ (incl (λ ((x ∢ xp) , y) → {!!})) ⟩-∼
                              ⋁ (λ (x : ⦋ false ↓[ Open' ] b ⦌) -> Open' ⟨ x ⟩) ∎
          lem-2 {true} {b} = {!!}




-- topological 𝒪' Open' (false) (true) (_and_) union refl refl (λ {u} {v} -> lem-1 {u} {v}) (λ {B} {U} -> lem-2 {B} {U})
--     where 𝒪' = Bool
--           Open' : 𝔹 -> _
--           Open' (true) = ⊤
--           Open' (false) = ⊥

--           union : {B : 𝒰 𝑖} → GoodFamily Open' B → 𝒪'
--           union F with decideBase (of F)
--           ... | left x = false
--           ... | just x = true

--           lem-1 : {u v : 𝒪'} → Open' (u and v) ∼ Open' u ∧ Open' v
--           lem-1 {false} {v} = absorb-l-∧ ⁻¹
--           lem-1 {true} {v} = unit-l-∧ ⁻¹

--           lem-2 : {B : 𝒰 𝑖} {U : GoodFamily Open' B} →
--                   Open' (union U) ∼ (⋁ (Open' ∘ ⟨ U ⟩))
--           lem-2 {B} {U} with decideBase (of U)
--           ... | left x = empty-⋁ x ⁻¹
--           ... | just b =
--                    ⊤                       ⟨ absorb-r-∨ ⁻¹ ⟩-∼
--                    (⋁ (Open' ∘ ⟨ U ⟩)) ∨ ⊤ ⟨ duplicate-r-⋁ b P ⟩-∼
--                    (⋁ (Open' ∘ ⟨ U ⟩))      ∎
--                 where P : Open' (⟨ U ⟩ b) ∼ ⊤
--                       P with  ⟨ U ⟩ b | noEmpties (of U) b
--                       ... | true | Y = refl

