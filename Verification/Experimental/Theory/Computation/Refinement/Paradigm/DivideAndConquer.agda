
module Verification.Experimental.Theory.Computation.Problem.Paradigm.DivideAndConquer where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition
-- open import Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat


---------------------------------------------------------------
-- Every problem can be turned into the problem of
-- finding a divide and conquer solution

record DivideAndConquer (Π : Problem 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor dac
  field original : ⟨ Π ⟩
open DivideAndConquer {{...}} public

record DivideAndConquerProp (Π : Problem 𝑖) (P : DivideAndConquer Π -> 𝒰 (fst 𝑖)) : 𝒰 (fst 𝑖 ､ (snd 𝑖) ⁺) where
  field Size : WFT (ℓ₀ , ℓ₀)
  field size : (∑ P) -> ⟨ Size ⟩
  -- field originalP : 𝒱 {{of Π}} (P ∣ dac)
--   -- field ∂ : ⟨ Π ⟩ -> ∑ λ n -> Fin-R n -> ⟨ Π ⟩
--   -- field size-∂ : ∀ p -> ∀ i -> size (∂ p .snd i) ≪ size p

open DivideAndConquerProp {{...}} public

DAC : ∀ (Π : Problem 𝑖) -> SomeStructure
DAC Π = structureOn (DivideAndConquer Π)

instance
  isProblem:DAC : ∀{Π : Problem 𝑖} -> isProblem (𝑖 ⌄ 1) (DAC Π)
  isProblem:DAC {Π = Π} = record
    { 𝒱 = DivideAndConquerProp Π
    }

ぶん : Problem 𝑖 -> Problem 𝑖
ぶん Π = DAC Π

分 : ∀ {𝑖} -> SomeStructure
分 {𝑖} = structureOn (ぶん {𝑖})


private
  module _ {Π : Problem 𝑖} where
    ε : DAC Π -> ⟨ Π ⟩
    ε x = x .original

    -- η : ⟨ Π ⟩ -> DAC Π
    -- η x = dac x

    instance
      isReduction:η : isReduction (DAC Π) Π ε
      isReduction:η = record
        { valid = λ P x → {!!}
        }
        -- { propMap = λ P x → let y = originalP {{x}}
        --                     in {!!}
        -- ; solutionMap = {!!}
        -- }

-- η-分 : ∀{Π : Problem 𝑖} -> 分 Π ⟶ Π
-- η-分 = incl ′ η ′













































