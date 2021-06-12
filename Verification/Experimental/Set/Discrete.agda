
module Verification.Experimental.Set.Discrete where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Prop.Everything


record isDiscrete-∼ (A : 𝒰 𝑖) {{_ : isSetoid 𝑗 A}} : 𝒰 (𝑗 ､ 𝑖) where
  field _≟-∼_ : (a b : A) -> Decision (a ∼ b)
open isDiscrete-∼ {{...}} public

record isSet-Str (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field isset-Str : ∀{a b : A} -> (p q : a ≡-Str b) -> p ≡-Str q
open isSet-Str {{...}} public

record isDiscrete' (A : 𝒰 𝑖) : 𝒰 (𝑖) where
  field {{decidableEquality}} : ∀{a : A} -> is𝒫-Dec (λ b -> ∣ a ≡-Str b ∣)
open isDiscrete' {{...}} public

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  instance
    isDiscrete':+ : {{_ : isDiscrete' A}} {{_ : isDiscrete' B}} -> isDiscrete' (A +-𝒰 B)
    isDiscrete'.decidableEquality isDiscrete':+ = {!!}

