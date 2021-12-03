
module Verification.Core.Data.List.Dependent.Variant.Base.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.Nat.Free

open import Verification.Core.Data.List.Variant.Base.Definition


-- lists
module _ {A : 𝒰 𝑖} where
  data _∍♮_ : ∀(as : List A) -> (a : A) -> 𝒰 𝑖 where
    incl : ∀{a bs} -> (a ∷ bs) ∍♮ a
    skip : ∀{a b bs} -> bs ∍♮ a ->  (b ∷ bs) ∍♮ a



-- dependent lists

module _ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) where
  data DList : (as : List A) -> 𝒰 (𝑖 ､ 𝑗) where
    [] : DList []
    _∷_ : ∀{a as} -> (b : B a) -> (bs : DList as) -> DList (a ∷ as)

ConstDList : (A : 𝒰 𝑖) (n : ♮ℕ) -> 𝒰 _
ConstDList A = DList (const A)


