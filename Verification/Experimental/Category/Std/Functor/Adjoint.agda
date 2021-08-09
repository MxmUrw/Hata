
module Verification.Experimental.Category.Std.Functor.Adjoint where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isAdjoint (F : Functor 𝒞 𝒟) (G : Functor 𝒟 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field adj    : ∀{a : ⟨ 𝒟 ⟩} -> ⟨ F ⟩ (⟨ G ⟩ a) ⟶ a
    field coadj  : ∀{a : ⟨ 𝒞 ⟩} -> a ⟶ ⟨ G ⟩ (⟨ F ⟩ a)

  open isAdjoint {{...}} public


  module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} {{_ : isAdjoint F G}} where

    -- |> For any two objects [..] and [..],
    module _ {a : ⟨ 𝒞 ⟩} {b : ⟨ 𝒟 ⟩} where

      -- |> we have an isomorphism between hom-types as follows:
      free : (a ⟶ ⟨ G ⟩ b) -> (⟨ F ⟩ a ⟶ b)
      free f = map f ◆ adj

      -- | The inverse direction is given by:
      cofree : (⟨ F ⟩ a ⟶ b) -> (a ⟶ ⟨ G ⟩ b)
      cofree f = coadj ◆ map f










