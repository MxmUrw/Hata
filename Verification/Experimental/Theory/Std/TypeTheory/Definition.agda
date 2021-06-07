
module Verification.Experimental.Theory.Std.TypeTheory.Definition where

open import Verification.Experimental.Conventions hiding (Forget)
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
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Computation.Question.Construction.Product
open import Verification.Experimental.Theory.Std.Theory.Definition

--------------------------------------------------------------------
-- The type theoretical perspective on a theory

record isTypeTheory (𝑖 : 𝔏 ^ 3) (Type : 𝒰' 𝑗) : 𝒰' (𝑖 ⁺ ､ 𝑗) where
  constructor typeTheory


  field Termᵘ : 𝒰 (𝑖 ⌄ 0)
  field {{isSetoid:Term}} : isSetoid (𝑖 ⌄ 1) Termᵘ

  field _∶_ : Termᵘ -> Type -> 𝒰 (𝑖 ⌄ 2)
  field preserveType : ∀ {t₁ t₂} -> (t₁ ∼ t₂) -> ∀{τ : Type} -> t₁ ∶ τ -> t₂ ∶ τ

  macro Term = #structureOn Termᵘ

  TypedTermᵘ : Type -> 𝒰 _
  TypedTermᵘ τ = (∑ λ (t : Term) -> t ∶ τ)

  instance
    isSetoid:TypedTerm : ∀{τ : Type} -> isSetoid (𝑖 ⌄ 0) (TypedTermᵘ τ)
    isSetoid:TypedTerm = {!!}


  -- TTerm : Type -> Setoid _
  -- TTerm τ = (∑ λ (t : Term) -> t ∶ τ) since record { _∼'_ = λ (t , _) (s , _) -> t ∼ s ; isEquivRel:∼ = {!!} }

open isTypeTheory {{...}} public

TypeTheory : (𝑖 : 𝔏 ^ 4) -> 𝒰 _
TypeTheory 𝑖 = (𝒰 (𝑖 ⌄ 0)) :& isTypeTheory (𝑖 ⌄ 1 ⋯ 3)


-- private
ForgetTT : TypeTheory 𝑖 -> Theory _
ForgetTT 𝓣  = ⟨ 𝓣 ⟩ since theory λ τ → TypedTermᵘ τ

-- instance Register:ForgetTypeTheory = register[ "" , 𝑖 ] ForgetTT {𝑖}

instance
  Register:ForgetTypeTheory = register₁[ "" , 𝑖 ] (ForgetTT {𝑖})


---------------------------------------------------------------
-- the categorical structure

--  -> Category _
-- macro
--   TT : ∀ {𝑖} -> SomeStructure
--   TT {𝑖} = #structureOn (FullSubcategory (ForgetTT {𝑖}))

-- instance
--   isCategory:Theory : isCategory (_ , 𝑖 ⌄ 0) (TypeTheory 𝑖)
--   isCategory:Theory = category TypeTheoryHom {{{!!}}} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}






