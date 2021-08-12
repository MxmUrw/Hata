
module Verification.Experimental.Category.Std.RelativeMonad.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isRelativeMonad (J : Functor 𝒞 𝒟) (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    constructor relativemonad
    field repure : ∀{a : ⟨ 𝒞 ⟩} -> ⟨ J ⟩ a ⟶ ⟨ F ⟩ a
    field reext : ∀{a b : ⟨ 𝒞 ⟩} -> (f : ⟨ J ⟩ a ⟶ ⟨ F ⟩ b) -> ⟨ F ⟩ a ⟶ ⟨ F ⟩ b
    field reunit-l : ∀{a b : ⟨ 𝒞 ⟩} -> {f : ⟨ J ⟩ a ⟶ ⟨ F ⟩ b} -> repure ◆ reext f ∼ f
    field reunit-r : ∀{a : ⟨ 𝒞 ⟩} -> reext (repure {a = a}) ∼ id
    field reassoc : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : ⟨ J ⟩ a ⟶ ⟨ F ⟩ b} {g : ⟨ J ⟩ b ⟶ ⟨ F ⟩ c} -> reext f ◆ reext g ∼ reext (f ◆ reext g)


  open isRelativeMonad {{...}} public

  module _ (J : Functor 𝒞 𝒟) where
    RelativeMonad = _ :& isRelativeMonad J






