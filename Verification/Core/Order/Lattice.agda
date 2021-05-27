
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Order.Lattice where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Partialorder
open import Verification.Core.Order.Preorder


record has⊥-Preorder (A : 𝒰 𝑖) {{_ : IPreorder A}} : 𝒰 𝑖 where
-- record has⊥-Preorder (A : Preorder 𝑖) : 𝒰 𝑖 where
  field ⊥ : A
        initial-⊥ : ∀(a : A) -> ⊥ ≤ a

open has⊥-Preorder {{...}} public

record has∨-Preorder (A : 𝒰 𝑖) {{_ : IPreorder A}} : 𝒰 𝑖 where
  field _∨_ : A -> A -> A
        ι₀-∨ : {a b : A} -> a ≤ a ∨ b
        ι₁-∨ : {a b : A} -> b ≤ a ∨ b
        [_,_]-∨ : {a b c : A} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

  infixl 60 _∨_

open has∨-Preorder {{...}} public

module _ {A : 𝒰 𝑖} {{_ : IPreorder A}} {{_ : has⊥-Preorder A}} {{_ : has∨-Preorder A}} where
  ⋁ : Vec A n -> A
  ⋁ [] = ⊥
  ⋁ (a ∷ as) = a ∨ (⋁ as)


-- record IJoinLattice (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
--   field {{Impl}} : IPartialorder A
--         _∨_ : A -> A -> A
--         ι₀-∨ : {a b : A} -> a ≤ a ∨ b
--         ι₁-∨ : {a b : A} -> b ≤ a ∨ b
--         ⊥ : A
--         initial-⊥ : ∀{a : A} -> ⊥ ≤ a

--   infixl 60 _∨_

-- unquoteDecl JoinLattice joinLattice = #struct "JLat" (quote IJoinLattice) "A" JoinLattice joinLattice

-- open IJoinLattice {{...}} public

-- instance
--   IJoinLattice:⊤ : IJoinLattice (Lift {j = 𝑖} 𝟙-𝒰)
--   IJoinLattice.Impl IJoinLattice:⊤ = IPartialorder:⊤
--   IJoinLattice._∨_ IJoinLattice:⊤ = λ _ _ -> ↥ tt
--   IJoinLattice.ι₀-∨ IJoinLattice:⊤ = ↥ tt
--   IJoinLattice.ι₁-∨ IJoinLattice:⊤ = ↥ tt
--   IJoinLattice.⊥ IJoinLattice:⊤ = ↥ tt
--   IJoinLattice.initial-⊥ IJoinLattice:⊤ = ↥ tt





