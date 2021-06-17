
module Verification.Experimental.Category.Multi.Category.Free.Strict where

open import Verification.Conventions hiding (ℕ)
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Set.Finite.ReachableSubsets.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Algebra.Monoid.Definition

open import Verification.Experimental.Category.Multi.Graph.Definition
open import Verification.Experimental.Category.Multi.Category.Definition


module _ {A : 𝒰 _} {{_ : Monoid 𝑖 on A}} where
  ⭑_ : (𝔽ʳ n -> A) -> A
  ⭑_ {zero} as = ◌
  ⭑_ {suc n} as = as zero ⋆ (⭑ (as ∘ suc))


module _ {A : ℕ} {B : 𝔽ʳ A -> ℕ} {C : 𝒰 𝑖}where
  uncurry-𝔽ʳ : (∀(a : 𝔽ʳ A) -> (b : 𝔽ʳ (B a)) -> C) -> ∀ (x : 𝔽ʳ (⭑ B)) -> C
  uncurry-𝔽ʳ f x = {!!}

module _ (G : MultiGraph 𝑖) where
  data FreeHomᵐ : {A : 𝒰₀} -> {{_ : isFinite A}} -> (A -> ⟨ G ⟩) -> ⟨ G ⟩ -> 𝒰 (𝑖 ⁺) where
    idᵐ-Free : ∀{g : ⟨ G ⟩} -> FreeHomᵐ {𝔽ʳ 1} (const g) g
    ιᵐ-Free : ∀{n : ℕ} {o : Fin-R n -> ⟨ G ⟩} {g : ⟨ G ⟩} -> (Edgeᵐ o g)
              -> FreeHomᵐ o g
    compᵐ-Free : ∀{A : 𝒰₀} -> {B : A -> 𝒰₀}
               -- the finiteness proofs
                  -> {{_ : isFinite A}} -> {{_ : ∀{a : A} -> isFinite (B a)}}
               -- the objects
                  -> {x : ⟨ G ⟩} -> {y : A -> ⟨ G ⟩} {z : ∀(a : A) -> B a -> ⟨ G ⟩}
               -- the homs
                  -> FreeHomᵐ y x
                  -> (∀{a : A} -> FreeHomᵐ (z a) (y a))
                  -> FreeHomᵐ (uncurry z) x


  data FreeHomᵐ-↓ : {A : 𝒰₀} -> {{_ : isFinite A}} -> (A -> ⟨ G ⟩) -> ⟨ G ⟩ -> 𝒰 (𝑖 ⁺) where
    idᵐ-Free : ∀{g : ⟨ G ⟩} -> FreeHomᵐ-↓ {𝔽ʳ 1} (const g) g
    compᵐ-Free : ∀{A : 𝒰₀} -> {B : A -> 𝒰₀}
               -- the finiteness proofs
                  -> {{_ : isFinite A}} -> {{_ : ∀{a : A} -> isFinite (B a)}}
               -- the objects
                  -> {x : ⟨ G ⟩} -> {y : A -> ⟨ G ⟩} {z : ∀(a : A) -> B a -> ⟨ G ⟩}
               -- the homs
                  -> Edgeᵐ (y ∘ fromFin) x
                  -> (∀{a : A} -> FreeHomᵐ-↓ (z a) (y a))
                  -> FreeHomᵐ-↓ (uncurry z) x




{-

  private
    module _ {n} {t : Fin-R n -> ⟨ G ⟩} {h : ⟨ G ⟩} where

      normalise : FreeHomᵐ t h -> FreeHomᵐ-↓ t h
      normalise idᵐ-Free = idᵐ-Free
      normalise (ιᵐ-Free x) = {!!}
      normalise (compᵐ-Free idᵐ-Free y) = {!!}
      normalise (compᵐ-Free (ιᵐ-Free x) y) = compᵐ-Free x (λ {a} -> {!!})
      normalise (compᵐ-Free (compᵐ-Free x x₁) y) = {!!}

-}
