

module Verification.Core.Category.Multi.Category.Definition where

open import Verification.Conventions
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Finite.ReachableSubsets.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice


--
-- Definition based on
-- https://github.com/agda/agda-categories/blob/master/src/Categories/Multi/Category/Indexed.agda
--
-- (MIT)-License and copyright as described there.
--



module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {C : ∀{a} -> B a -> 𝒰 𝑘} where
  uncurry : (∀(a : A) -> (b : B a) -> C b) -> ∀ (x : ∑ B) -> C (x .snd)
  uncurry f (a , b) = f a b



record isMultiCategory (𝑗 : 𝔏) (ℳ : 𝒰 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Homᵐ : ∀{A : 𝒰₀} {{_ : isFinite A}} -> (A -> ℳ) -> ℳ -> 𝒰 𝑗
        idᵐ : ∀{a : ℳ} -> Homᵐ {𝔽ʳ 1} (const a) a
        _◆ᵐ_ : ∀{A : 𝒰₀} -> {B : A -> 𝒰₀}
               -- the finiteness proofs
                  -> {{_ : isFinite A}} -> {{_ : ∀{a : A} -> isFinite (B a)}}
               -- the objects
                  -> {x : ℳ} -> {y : A -> ℳ} {z : ∀(a : A) -> B a -> ℳ}
               -- the homs
                  -> Homᵐ y x
                  -> (∀{a : A} -> Homᵐ (z a) (y a))
                  -> Homᵐ (uncurry z) x


open isMultiCategory {{...}} public

-- module _ {𝒞 : 𝒰 𝑖} {{_ : isMultiCategory 𝑗 𝒞}} where
--   compose-l : ∀{x : 𝒞} -> (c : ComposeObjects Hom-MC 2 x) -> Hom-MC (alltails Hom-MC c .fst) (alltails Hom-MC c .snd) x
--   compose-l = {!!}


