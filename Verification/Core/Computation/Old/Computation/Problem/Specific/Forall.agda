
module Verification.Core.Theory.Computation.Problem.Specific.Forall where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Computation.Problem.Definition

--------------------------------------------------
-- The main forall problem

record ForallProblem (𝑖 : 𝔏 ^ 2) : 𝒰 (𝑖 ⁺) where
  constructor forallP
  field Base : 𝒰 (𝑖 ⌄ 0)
  field Statement : Base -> 𝒰 (𝑖 ⌄ 1)

open ForallProblem public

ForallSolution : (ForallProblem 𝑖) -> 𝒰 _
ForallSolution P = ∀ a -> P .Statement a

macro
  FORALL : ∀ 𝑖 -> SomeStructure
  FORALL 𝑖 = #structureOn (ForallProblem 𝑖)

instance
  isProblem:FORALL : isProblem _ (FORALL 𝑖)
  isProblem:FORALL = problem (ForallSolution)

instance
  hasU:ForallProblem : ∀{𝑖} -> hasU (ForallProblem 𝑖) _ _
  hasU:ForallProblem = hasU:Base (ForallProblem _)

--------------------------------------------------
-- Solving forall via induction

record isDivideAndConquer {𝑖} (π : ForallProblem 𝑖) : 𝒰 (ℓ₀ ⁺ ､ 𝑖) where
  constructor divideAndConquerP
  field Size : WFT (ℓ₀ , ℓ₀)
  field size : Base π -> ⟨ Size ⟩
  field split : Base π -> ∑ λ n -> Fin-R n -> Base π
  field split-size : ∀(π) -> ∀ i -> size (split π .snd i) ≪ size π

open isDivideAndConquer {{...}} public

DivideAndConquer : ∀ 𝑖 -> 𝒰 _
DivideAndConquer 𝑖 = ForallProblem 𝑖 :& isDivideAndConquer

macro
  DAC : ∀ 𝑖 -> SomeStructure
  DAC 𝑖 = #structureOn (DivideAndConquer 𝑖)

instance
  isProblem:DAC : isProblem _ (DAC 𝑖)
  isProblem:DAC = problem (λ π → ∀ b -> (∀ i -> ⟨ π ⟩ .Statement (split {{of π}} b .snd i)) -> ⟨ π ⟩ .Statement b)

module _ where
  private
    f : DAC 𝑖 -> FORALL 𝑖
    f π = ⟨ π ⟩

  macro
    分 : ∀ {𝑖} -> SomeStructure
    分 {𝑖} = #structureOn (f {𝑖})

instance
  isDeductive:分 : isDeductive (DAC 𝑖) (FORALL 𝑖) 分
  isDeductive:分 = deductive {!!}


