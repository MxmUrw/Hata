
module Verification.Experimental.Theory.Std.ComputationalTheory.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Category.Std.Graph.Definition
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

-- record Repr (A : Setoid 𝑖) (P : ⟨ A ⟩ -> 𝒰 𝑘) (a : ⟨ A ⟩) : 𝒰 (𝑖 ､ 𝑘) where
--   constructor mkrepr
--   field ⟨_⟩ : ⟨ A ⟩
--   field represents : a ∼ ⟨_⟩
--   field hasProperty : P ⟨_⟩
-- open Repr public

-- record hasRepr (A : Setoid 𝑖) (P : ⟨ A ⟩ -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
--   field repr : ∀(a : ⟨ A ⟩) -> Repr A P a
-- open hasRepr public

--------------------------------------------------------------------
-- theory with computational interpretation

-- private macro
--   U = instance[ "forget" , 𝑖 ] (Category 𝑖 -> 𝒰 _) ◀

record isComputational {𝑗 : 𝔏 ^ 2} {𝑖} (𝓒 : 𝒰 𝑖) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  constructor computational
  field CompTerm : 𝓒 -> 𝒰 (𝑗 ⌄ 0)
  field {{isGraph:CompTerm}} : ∀ {c} -> isGraph {𝑗 ⌄ 1} (CompTerm c)

open isComputational {{...}} public

Computational : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Computational 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isComputational {𝑖 ⌄ 1 , 𝑖 ⌄ 2}

Computational→Theory : Computational 𝑖 -> Theory _
Computational→Theory 𝓒 = ⟨ 𝓒 ⟩ since theory CompTerm {{λ {c} -> of S ′ CompTerm c ′}}
  where private macro
    S = instance[ "" , 𝑖 ] (Graph 𝑖 -> Setoid _) ◀


-- Computational : (𝑖 : 𝔏 ^ 5) -> 𝒰 _
-- Computational 𝑖 = Theory (𝑖 ⌄ 0 , 𝑖 ⌄ 1 , 𝑖 ⌄ 2) :& isComputational (𝑖 ⌄ 3 , 𝑖 ⌄ 4)





{-
record isComputational (𝑗 : 𝔏 ^ 2) (𝓣 : Theory 𝑖) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  constructor computational
  field isNormal : ∀{ϕ : ⟨ 𝓣 ⟩} -> ⟨ ϕ ■ ⟩ -> 𝒰 (𝑗 ⌄ 0)

  _■N : ⟨ 𝓣 ⟩ -> 𝒰 _
  _■N ϕ = ∑ λ (p : ⟨ ϕ ■ ⟩) -> isNormal p

  field normalize : ∀ (ϕ : ⟨ 𝓣 ⟩) -> hasRepr (ϕ ■) isNormal
  field isCanonical : ⟨ 𝓣 ⟩ -> 𝒰 (𝑗 ⌄ 1)
  Canonical : 𝒰 _
  Canonical = ∑ isCanonical
  field _⇛_ : Canonical -> Canonical -> ⟨ 𝓣 ⟩
  infix 100 _⇛_
  field run : ∀{a b : Canonical} -> ⟨ (a ⇛ b) ■ ⟩ -> a .fst ■N -> b .fst ■N
  normalize' : ∀ {ϕ : ⟨ 𝓣 ⟩} -> ⟨ ϕ ■ ⟩ -> ϕ ■N
  normalize' = {!!}

  -- field can : Canonical -> ⟨ 𝓣 ⟩


-- maps between computational theories
record isComputationalHom (𝓒 : Computational 𝑖) (𝓓 : Computational 𝑗) (F : TheoryHom ′ ⟨ 𝓒 ⟩ ′ ′ ⟨ 𝓓 ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where
  constructor computationalHom
  field isNormal-■N : ∀(ϕ : ⟨ 𝓒 ⟩) -> (t : ϕ ■N) -> isNormal (⟨ map-■ {{of F}} ϕ ⟩ (t .fst))

  map-■N : ∀(ϕ : ⟨ 𝓒 ⟩) -> ϕ ■N -> ⟨ ⟨ F ⟩ ϕ ■ ⟩
  map-■N ϕ t = (⟨ map-■ {{of F}} ϕ ⟩ (t .fst))
  -- , isNormal-■N _ t

  field canonical : ∀{ϕ : ⟨ 𝓒 ⟩} -> isCanonical ϕ -> isCanonical (⟨ F ⟩ ϕ) -> isIso-𝒰 (map-■N ϕ)



record Meta 𝑖 : 𝒰 (𝑖 ⁺) where
  constructor meta
  field fst : 𝒰 𝑖
  field snd : 𝒰 𝑖

macro
  𝗠𝗲𝘁𝗮 : ∀ 𝑖 -> SomeStructure
  𝗠𝗲𝘁𝗮 𝑖 = #structureOn (Meta 𝑖)

-- 𝗠𝗲𝘁𝗮
-- ℳℯ𝓉𝒶
-- 𝒜𝓈𝓂

instance
  isTheory:𝗠𝗲𝘁𝗮 : isTheory _ (𝗠𝗲𝘁𝗮 𝑖)
  isTheory:𝗠𝗲𝘁𝗮 = theory λ (meta a b) → (a ⟶ b) since isSetoid:Hom


instance
  isComputational:𝗠𝗲𝘁𝗮 : isComputational _ (𝗠𝗲𝘁𝗮 𝑖)
  isComputational:𝗠𝗲𝘁𝗮 = computational (const 𝟙-𝒰) R (const 𝟙-𝒰) (λ (A , _) (B , _) → {!!}) {!!}
    where R = {!!}



-}


