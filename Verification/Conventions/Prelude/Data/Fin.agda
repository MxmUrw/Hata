
module Verification.Conventions.Prelude.Data.Fin where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.Nat

open import Verification.Conventions.Prelude.Data.FinData.Base renaming (Fin to Fin-R ; toℕ to toℕ-Fin-R ; ¬Fin0 to ¬Fin0-R) public


≤→Fin : ∀{a b} -> {{_ : a ≤-ℕ-Dec b}} -> (Fin-R (suc b))
≤→Fin {a = zero} {{p}} = zero
≤→Fin {a = suc a} {.(suc _)} {{suc {{p}}}} = suc (≤→Fin {{p}})


