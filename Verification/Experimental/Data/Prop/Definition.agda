
module Verification.Experimental.Data.Prop.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure

record Prop (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  -- no-eta-equality
  constructor ∣_∣-Prop
  field ⟨_⟩ : 𝒰 𝑖
open Prop public

instance
  Notation-Absolute:Prop : Notation-Absolute (𝒰 𝑖) (Prop 𝑖)
  Notation-Absolute.∣_∣ Notation-Absolute:Prop = ∣_∣-Prop


𝒫 : 𝒰 𝑖 -> 𝒰 (𝑖 ⁺)
𝒫 {𝑖} A = A -> Prop 𝑖

record ⦋_⦌ {U : 𝒰 𝑖} (P : U -> Prop 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  constructor _∢_
  field ⟨_⟩ : U
  field Proof : Prop.⟨_⟩ (P ⟨_⟩)
open ⦋_⦌ public

infix 60 _∢_

-- _⋲ 	⋳ 	⋴ 	⋵ 	⋶ 	⋷ 	⋸ 	⋹ 	⋺ 	⋻ 	⋼ 	⋽ 	⋾ 	⋿
--  	∢ ∡ ∢

_∈_ : {A : 𝒰 𝑙} -> (a : A) -> {U : 𝒰 𝑖} -> (u : U) -> {{UU : hasU U (𝑗 ⁺ ⊔ 𝑙) 𝑘}} -> {{_ : getU UU ≡-Str (A -> Prop 𝑗)}} -> 𝒰 𝑗
_∈_ a u {{UU}} {{p}} with destructEl UU u | p
... | f | refl-StrId = ⟨ f a ⟩


infix 1 exists

exists : ∀{A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> Prop (ℓ ⊔ ℓ')
exists B = ∣ ∑ B ∣

syntax exists (λ x -> F) = ∃ x , F

-- module _  where
existsIn : {A : 𝒰 𝑙} {U : 𝒰 𝑖} -> (u : U) -> {{UU : hasU U (𝑗 ⁺ ⊔ 𝑙) 𝑘}} {{_ : getU UU ≡-Str (A -> Prop 𝑗)}} -> (C : A -> 𝒰 𝑖₁) -> Prop (𝑙 ､ 𝑗 ､ 𝑖₁)
existsIn u C = ∣ ∑ (λ a -> (a ∈ u) ×-𝒰 C a) ∣

syntax existsIn U (λ x -> F) = ∃ x ∈ U , F


