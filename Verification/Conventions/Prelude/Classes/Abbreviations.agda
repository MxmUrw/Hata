

module Verification.Conventions.Prelude.Classes.Abbreviations where

open import Verification.Conventions.Proprelude

record INotation:Algebra (A : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ⊔ (𝑗 ⁺)) where
  field _-Alg : A -> 𝒰 𝑗
  infix 400 _-Alg
open INotation:Algebra {{...}} public

-- record INotation:Forget (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
--   field Forget : A -> B
-- open INotation:Forget {{...}} public

-- record INotation:Free (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
--   field Free : A -> B
-- open INotation:Free {{...}} public

record INotation:Reinterpret (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  field reinterpret : A -> B
open INotation:Reinterpret {{...}} public

-- record INotation:Moule {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
--   field _-Mod : (a : A) -> P a
--   infix 400 _-Mod
-- open INotation:Module {{...}} public


