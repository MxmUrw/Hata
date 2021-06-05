
module Verification.Experimental.Theory.Std.TypeTheory.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.Category
open import Verification.Experimental.Data.Prop.Everything
-- open import Verification.Experimental.Data.Sum.Definition
-- open import Verification.Experimental.Data.Rational.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Computation.Question.Construction.Product
open import Verification.Experimental.Theory.Std.Theory.Definition



--------------------------------------------------------------------
-- The type theoretical perspective on a theory

record isTypeTheory (𝑖 : 𝔏 ^ 3) (Type : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  constructor typeTheory
  field Term : 𝒰 (𝑖 ⌄ 0)
  field {{isSetoid:Term}} : isSetoid (𝑖 ⌄ 1) Term
  field _∶_ : Term -> Type -> 𝒰 (𝑖 ⌄ 2)
  field preserveType : ∀ {t₁ t₂} -> (t₁ ∼ t₂) -> ∀{τ : Type} -> t₁ ∶ τ -> t₂ ∶ τ

  -- TypedTerm : Setoid _
  -- TypedTerm = (∑ λ (t : ⟨ Term ⟩) -> ∑ λ (τ : Type) -> t ∶ τ)
  --             since record { _∼'_ = λ (t , _) (s , _) -> t ∼ s ; isEquivRel:∼ = {!!} }

  TTerm : Type -> Setoid _
  TTerm τ = (∑ λ (t : Term) -> t ∶ τ) since record { _∼'_ = λ (t , _) (s , _) -> t ∼ s ; isEquivRel:∼ = {!!} }

open isTypeTheory {{...}} public

TypeTheory : (𝑖 : 𝔏 ^ 4) -> 𝒰 _
TypeTheory 𝑖 = (𝒰 (𝑖 ⌄ 0)) :& isTypeTheory (𝑖 ⌄ 1 , 𝑖 ⌄ 2 , 𝑖 ⌄ 3)

ttheo : TypeTheory 𝑖 -> Theory _
ttheo 𝓣  = ⟨ 𝓣 ⟩ since theory (λ τ → ⟨ TTerm τ ⟩) {{of TTerm _}}





