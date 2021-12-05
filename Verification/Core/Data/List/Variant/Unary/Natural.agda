
module Verification.Core.Data.List.Variant.Unary.Natural where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
-- open import Verification.Core.Data.Nat.Definition


-- [Remark]
-- | Lists of the type |List ⊤-𝒰|, where every element has to
--   be given by the only constructor |tt| of |⊤-𝒰|, are fully
--   determined by their length. An isomorphism |ℕ ≅ List ⊤-𝒰|
--   can be easily shown (NOTE: is this foreshadowing allowed?).
--   When using other list based constructions (such as?), it is then
--   easier to also use these as the definition of natural numbers,
--   for instance for specifying the length of a list.
-- | We give these lists a special name.

♮ℕᵘ : 𝒰₀
♮ℕᵘ = List ⊤-𝒰

-- #Notation/Rewrite# ♮ℕᵘ = ℕᵘ
-- //

-- [Hide]
macro ♮ℕ = #structureOn ♮ℕᵘ

ι-♮ℕ : ℕ -> ♮ℕ
ι-♮ℕ zero = []
ι-♮ℕ (suc n) = tt ∷ ι-♮ℕ n

instance
  fromNat♮ℕ : HasFromNat ♮ℕ
  fromNat♮ℕ = record { Constraint = λ _ → 𝟙-𝒰 ; fromNat = λ n -> ι-♮ℕ n }

instance
  isSetoid:♮ℕ : isSetoid ♮ℕ
  isSetoid:♮ℕ = isSetoid:byId
-- //


