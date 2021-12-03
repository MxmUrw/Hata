
module Verification.Core.Data.List.Dependent.Variant.Base.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Nat.Free

open import Verification.Core.Data.List.Variant.Base.Definition

-- dependent lists



module _ {A : 𝒰 𝑖} where
  mutual
    syntax Listᴰ (λ a -> B) as = List[ a ∈ as ] B

    data Listᴰ (B : A -> 𝒰 𝑗) : (as : List A) -> 𝒰 (𝑖 ､ 𝑗) where
      -- [] : Listᴰ B []
      -- _∷_ : ∀{a as} -> (b : B a) -> (bs : Listᴰ B as) -> Listᴰ B (a ∷ as)
      [] : List[ a ∈ [] ] B a
      _∷_ : ∀{a as} -> (b : B a) -> (bs : List[ a ∈ as ] B a) -> List[ a ∈ (a ∷ as) ] B a



ConstListᴰ : (A : 𝒰 𝑖) (n : ♮ℕ) -> 𝒰 _
ConstListᴰ A = Listᴰ (const A)


