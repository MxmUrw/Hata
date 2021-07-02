
module Verification.Experimental.Theory.Std.Generic.Theory.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition

-- =* Theories


-- | The purpose of this /theory of theories/ is to explicitly describe a framework in
-- which all efforts in the area of syntax and semantics of type theories and programming languages
-- can be located. We want to include everything one would intuitively expect to be part of such research.
-- Thus we necessarily end up with a very rudimentary picture, based on a least common denominator.
-- Such a picture does not help with proving new theorems, and will not be surprising to anyone familiar
-- with the usual concepts and goals. In fact it should merely reflect this state of mind in a formal environment.

-- | We follow the common notion that a (type) theory may be viewed from the following perspectives:
-- | - /Type Theory/: A formal system with a set of terms and types, and a typing judgement relating them with each other.
-- | - /Category/: A set of objects, and sets of arrows between them, encoding the notion of composition.
-- | - /Computational Model/: A set of (possibly typed) terms with rewriting rules between them.


-- |: The "best" type theories (simple type theory, dependent type theory) incorporate all of these perspectives,
-- and this is known as /computational trilogy/. But our goal at the moment is not to describe the "best" type theories,
-- but to give a definition which subsumes anything which looks like a theory at all. Our attempt at describing the least common denominator
-- between the three perspectives is as follows:





-- #Notation/Rewrite# ■ᵘ = □
-- #Notation/Rewrite# ■ = □

-- #Notation/SemanticCategory# \mathbf{Mon} = Monoid
-- #Notation/Annotatable# assoc

_◀Str : (SomeStructure) -> SomeStructure
_◀Str a = a


-- [Definition]
-- | A theory is given by:
record isTheory (𝑖 : 𝔏 ^ 2) (𝓣 : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  constructor theory

  field _■ᵘ : 𝓣 -> 𝒰 (𝑖 ⌄ 0)
  field {{isSetoid:■}} : ∀{τ} -> isSetoid {𝑖 ⌄ 1} (τ ■ᵘ)

  macro _■ = λ (τ : 𝓣) -> #structureOn (τ ■ᵘ)

  -- -------
  -- -- fixities
  infix 80 _■ _■ᵘ

-- //

open isTheory {{...}} public

Theory : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Theory 𝑖 = (𝒰 (𝑖 ⌄ 0)) :& isTheory (𝑖 ⌄ 1 , 𝑖 ⌄ 2)

-- maps between theories

record isTheoryHom (𝓢 : Theory 𝑖) (𝓣 : Theory 𝑗) (F : ⟨ 𝓢 ⟩ -> ⟨ 𝓣 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  constructor theoryHom
  field map-■ : ∀(ϕ : ⟨ 𝓢 ⟩) -> SetoidHom (ϕ ■) (F ϕ ■)

open isTheoryHom {{...}} public

TheoryHom : (𝓢 : Theory 𝑖) (𝓣 : Theory 𝑗) -> 𝒰 _
TheoryHom 𝓢 𝓣 = _ :& isTheoryHom 𝓢 𝓣



instance
  isCategory:Theory : isCategory {_ , ⨆ 𝑖} (Theory 𝑖)
  isCategory:Theory = category TheoryHom {{{!!}}} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}



