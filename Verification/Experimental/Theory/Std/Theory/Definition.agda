
module Verification.Experimental.Theory.Std.Theory.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Experimental.Set.Discrete
-- open import Verification.Experimental.Set.Decidable
-- open import Verification.Experimental.Data.Universe.Everything
-- open import Verification.Experimental.Data.Universe.Instance.Category
-- open import Verification.Experimental.Data.Prop.Everything
-- open import Verification.Experimental.Data.Sum.Definition
-- open import Verification.Experimental.Data.Rational.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
-- open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Morphism.Iso


record isTheory (𝑖 : 𝔏 ^ 2) (𝓣 : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  constructor theory
  field _■ : 𝓣 -> 𝒰 (𝑖 ⌄ 0)
  field {{isSetoid:■}} : ∀{ϕ : 𝓣} -> isSetoid (𝑖 ⌄ 1) (ϕ ■)
  infix 80 _■

open isTheory {{...}} public

Theory : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Theory 𝑖 = (𝒰 (𝑖 ⌄ 0)) :& isTheory (𝑖 ⌄ 1 , 𝑖 ⌄ 2)

-- maps between theories

record isTheoryHom (𝓢 : Theory 𝑖) (𝓣 : Theory 𝑗) (F : ⟨ 𝓢 ⟩ -> ⟨ 𝓣 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  constructor theoryHom
  field map-■ : ∀ (ϕ : ⟨ 𝓢 ⟩) -> SetoidHom ′(ϕ ■)′ ′(F ϕ ■)′

open isTheoryHom {{...}} public

TheoryHom : (𝓢 : Theory 𝑖) (𝓣 : Theory 𝑗) -> 𝒰 _
TheoryHom 𝓢 𝓣 = _ :& isTheoryHom 𝓢 𝓣





