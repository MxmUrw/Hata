

module Verification.Core.Category.Functor.Adjunction where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Iso

-- module _ {X Y : Category 𝑖} where --  {Y : Category 𝑗} where
--   record IAdjoint2 (F : X ⟶ Y) (G : Y ⟶ X) : 𝒰 (⨆ 𝑖) where
--     field embed : Natural id (F ◆ G)
--           eval : Natural (G ◆ F) id

-- ===* Adjunction
-- | The concept of adjunctions is common throughout mathematics.

-- [Definition]
-- | Let [..] and [..] be two categories.
module _ {X : Category 𝑖} {Y : Category 𝑗} where
  -- |> We say that two functors are adjoint if:
  record IAdjoint (F : Functor X Y) (G : Functor Y X) : 𝒰 (𝑖 ､ 𝑗) where
    field embed : Natural id (comp-Cat F G)
          eval : Natural (comp-Cat G F) id
          reduce-Adj-β : ∀{a : ⟨ X ⟩} -> map (⟨ embed ⟩ {a}) ◆ ⟨ eval ⟩ ≣ id
          reduce-Adj-η : ∀{a : ⟨ Y ⟩} -> ⟨ embed ⟩ {⟨ G ⟩ a} ◆ map ⟨ eval ⟩ ≣ id
  open IAdjoint {{...}} public
-- //

-- [Notation]
-- | We will write [..],
  _⊣-Cat_ = IAdjoint

-- |> and also, for [..],
module _ {X Y : Category 𝑖} where
  -- |> we write:
  _⊣_ : (F : Functor X Y) (G : Functor Y X) -> 𝒰 𝑖
  F ⊣ G = F ⊣-Cat G
-- //

-- [Hide]
-- unquoteDecl hasAdjoint hasadjoint = #struct "Adj" (quote IAdjoint) "G" hasAdjoint hasadjoint
unquoteDecl hasRightAdjoint hasrightadjoint = #struct "RAdj" (quote IAdjoint) "G" hasRightAdjoint hasrightadjoint

module _ {X : Category 𝑖} {Y : Category 𝑗} where --  {Y : Category 𝑗} where
  hasLeftAdjoint : (G : Functor Y X) -> 𝒰 _
  hasLeftAdjoint G = Structure (λ F -> IAdjoint F G)
-- //

-- unquoteDecl hasLeftAdjoint hasleftadjoint = #struct "LAdj" (quote IAdjoint) "F" hasLeftAdjoint hasleftadjoint


-- module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where --  {Y : Category 𝑗} where
--   hasRightAdjoint : ∀(F : Functor 𝒞 𝒟) -> 𝒰 _
--   hasRightAdjoint F = ∑ λ G -> F ⊣-Cat G

--   hasLeftAdjoint : ∀(F : Functor 𝒞 𝒟) -> 𝒰 _
--   hasLeftAdjoint F = ∑ λ G -> G ⊣-Cat F

-- [Lemma]
-- | Let [..], and [..], [..] be two functors with [..].
module _ {X Y : Category 𝑖} {F : X ⟶ Y} {G : Y ⟶ X} {{_ : F ⊣ G}} where
  -- |> For any two objects [..] and [..],
  module _ {a : ⟨ X ⟩} {b : ⟨ Y ⟩} where
    -- |> we have an isomorphism between hom-types as follows:
    free : (a ⟶ ⟨ G ⟩ b) -> (⟨ F ⟩ a ⟶ b)
    free f = map f ◆ ⟨ eval ⟩
    -- | The inverse direction is given by:
    free⁻¹ : (⟨ F ⟩ a ⟶ b) -> (a ⟶ ⟨ G ⟩ b)
    free⁻¹ f = ⟨ embed ⟩ ◆ map f
-- //





