
module Verification.Experimental.Category.Std.Fibration.BaseChange.Definition where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Data.Universe.Everything


record hasBaseChange 𝑗 (𝒞 : Category 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
  constructor basechange
  field Change : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)

  _*! : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Functor (⟨ Change ⟩ b) (⟨ Change ⟩ a)
  _*! f = ⟨ map {{of Change}} (incl ⟨ f ⟩) ⟩

  field ∃! : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Functor (⟨ Change ⟩ a) (⟨ Change ⟩ b)
  field ∀! : ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> Functor (⟨ Change ⟩ a) (⟨ Change ⟩ b)

open hasBaseChange {{...}} public
  -- ∃!  ∀! *!







{-
record hasBaseChange (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⁺) where
  constructor basechange
  field MyTarget : 𝒰₀
  field myMap : ∀{a b : ⟨ 𝒞 ⟩} -> (a ⟶ b) -> MyTarget -> MyTarget

open hasBaseChange {{...}} public

instance
  hasBaseChange:Set1 : hasBaseChange (𝐓𝐲𝐩𝐞 𝑖)
  hasBaseChange:Set1 = basechange ℕ (const (const 1))

instance
  hasBaseChange:Set2 : hasBaseChange (𝐓𝐲𝐩𝐞 𝑖)
  hasBaseChange:Set2 = basechange Bool (const (const false))


mycall : Bool
mycall = myMap {a = ℕ} {b = ℕ} (id) true

-}
