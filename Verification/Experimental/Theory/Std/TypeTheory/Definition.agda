
module Verification.Experimental.Theory.Std.TypeTheory.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.Category
open import Verification.Experimental.Data.Prop.Everything
-- open import Verification.Experimental.Data.Sum.Definition
-- open import Verification.Experimental.Data.Rational.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full2
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Fibration.Specific.Fam.Definition
-- open import Verification.Experimental.Computation.Question.Construction.Product
open import Verification.Experimental.Theory.Std.Theory.Definition
open import Verification.Experimental.Computation.Question.Definition
open import Verification.Experimental.Computation.Question.Specific.Check

open import Verification.Experimental.Category.Std.Fibration.BaseChange.Definition
open import Verification.Experimental.Category.Std.Fibration.Definition
open import Verification.Experimental.Category.Std.Fibration.Instance.BaseChange

--------------------------------------------------------------------
-- The type theoretical perspective on a theory

record isTypeTheory (𝑖 : 𝔏 ^ 3) (Type : Set 𝑗) : 𝒰' (𝑖 ⁺ ､ 𝑗) where
  constructor typeTheory

  field Termᵘ : 𝒰 (𝑖 ⌄ 0)
  field {{isSetoid:Term}} : isSetoid (𝑖 ⌄ 1) Termᵘ

  field _∶_ : Termᵘ -> ⟨ Type ⟩ -> 𝒰 (𝑖 ⌄ 2)
  field preserveType : ∀ {t₁ t₂} -> (t₁ ∼ t₂) -> ∀{τ : ⟨ Type ⟩} -> t₁ ∶ τ -> t₂ ∶ τ

  macro Term = #structureOn Termᵘ

  TypedTermᵘ : ⟨ Type ⟩ -> 𝒰 _
  TypedTermᵘ τ = (∑ λ (t : Term) -> t ∶ τ)

  instance
    isSetoid:TypedTerm : ∀{τ : ⟨ Type ⟩} -> isSetoid (𝑖 ⌄ 0) (TypedTermᵘ τ)
    isSetoid:TypedTerm = {!!}


open isTypeTheory {{...}} public

TypeTheory : (𝑖 : 𝔏 ^ 4) -> 𝒰 _
TypeTheory 𝑖 = (Set (𝑖 ⌄ 0)) :& isTypeTheory (𝑖 ⌄ 1 ⋯ 3)


private
  Forget : TypeTheory 𝑖 -> Theory _
  Forget 𝓣  = ⟨ 𝓣 ⟩ since theory λ τ → TypedTermᵘ τ

instance
  Register:ForgetTypeTheory = register₁[ "" , 𝑖 ] (Forget {𝑖})

macro
  𝐓𝐓 : ∀(𝑖) -> SomeStructure
  𝐓𝐓 (𝑖) = #structureOn (TypeTheory 𝑖)

instance
  isCategory:𝐓𝐓 : isCategory _ (𝐓𝐓 𝑖)
  isCategory:𝐓𝐓 = isCategory:FullSubcategory Forget

---------------------------------------------------------------
-- Solved Type theories are ones for which the type checking
-- problem is solved

private
  Q : 𝐓𝐓 𝑖 -> 𝐐𝐮𝐞𝐬𝐭 _
  Q 𝓣 = (Term ×-𝒰 ⟨ 𝓣 ⟩) since answerWith (λ (t , τ) -> isDecidable (t ∶ τ))


𝐓𝐓Fam : ∀(𝑖) -> Family (𝐐𝐮𝐞𝐬𝐭 _) _
𝐓𝐓Fam 𝑖 = TypeTheory 𝑖 since family Q

private macro
  p = instance[ "" , 𝑖 / 3 ] (𝐅𝐚𝐦 (𝐐𝐮𝐞𝐬𝐭 (𝑖 ⌄ 0 ⋯ 1)) (𝑖 ⌄ 2) -> 𝐓𝐲𝐩𝐞 _) ◀

𝐓𝐓Fib : ∀ 𝑖 -> Fiber (p) (TypeTheory 𝑖)
𝐓𝐓Fib 𝑖 = 𝐓𝐓Fam _ since record { isSectionFiber = refl }


instance
  hasBaseChange:𝐓𝐲𝐩𝐞 : ∀ {𝑖 : 𝔏 ^ 3} -> hasBaseChange _ (𝐓𝐲𝐩𝐞 _)
  hasBaseChange:𝐓𝐲𝐩𝐞 {𝑖} = hasBaseChange:Fibration (p {𝑖})


---------------------------------------------------------------
-- the categorical structure

--  -> Category _
-- macro
--   TT : ∀ {𝑖} -> SomeStructure
--   TT {𝑖} = #structureOn (FullSubcategory (ForgetTT {𝑖}))

-- instance
--   isCategory:Theory : isCategory (_ , 𝑖 ⌄ 0) (TypeTheory 𝑖)
--   isCategory:Theory = category TypeTheoryHom {{{!!}}} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}






