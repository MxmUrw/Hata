
module Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Context where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Data.Universe.Everything


data Ctx-⦿ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  [] : Ctx-⦿ A
  _,,_ : (xs : Ctx-⦿ A) -> (x : A) -> Ctx-⦿ A
infixl 15 _,,_
pattern _;_ a b = _,,_ a b

Ctx = Ctx-⦿

module _ {A : 𝒰 𝑖} where
  data _⊢-Ctx-⦿_ : (Γ : Ctx-⦿ A) (a : A) -> 𝒰 𝑖 where
    zero : ∀{Γ a} -> (Γ ,, a) ⊢-Ctx-⦿ a
    suc : ∀{Γ a b} -> Γ ⊢-Ctx-⦿ a -> (Γ ,, b) ⊢-Ctx-⦿ a

module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-Ctx-⦿ : (f : A -> B) -> Ctx-⦿ A -> B
  rec-Ctx-⦿ f [] = ◌
  rec-Ctx-⦿ f (as ,, a) = rec-Ctx-⦿ f as ⋆ f a

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-Ctx-⦿ : (f : A -> B) -> Ctx-⦿ A -> Ctx-⦿ B
  map-Ctx-⦿ f [] = []
  map-Ctx-⦿ f (xs ,, x) = map-Ctx-⦿ f xs ,, f x



module _ (A : 𝒰 𝑖) where
  macro 𝖢-⦿ = #structureOn (Ctx-⦿ A)
  -- 𝖩-⦿
  -- 𝖱-⦿

module _ {A : 𝒰 𝑖} where
  _⋆-Ctx-⦿_ : Ctx-⦿ A -> Ctx-⦿ A -> Ctx-⦿ A
  a ⋆-Ctx-⦿ [] = a
  a ⋆-Ctx-⦿ (b ,, x) = a ⋆-Ctx-⦿ b ,, x


module _ {A : 𝒰 𝑖} where
  instance
    isSetoid:Ctx-⦿ : isSetoid (𝖢-⦿ A)
    isSetoid:Ctx-⦿ = isSetoid:byPath

    isMonoid:Ctx-⦿ : isMonoid (𝖢-⦿ A)
    isMonoid:Ctx-⦿ = record
                       { _⋆_ = _⋆-Ctx-⦿_
                       ; ◌ = []
                       ; unit-l-⋆ = {!!}
                       ; unit-r-⋆ = {!!}
                       ; assoc-l-⋆ = {!!}
                       ; _`cong-⋆`_ = {!!}
                       }

    isFunctor:Ctx-⦿ : isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖) Ctx-⦿
    isFunctor.map isFunctor:Ctx-⦿ = map-Ctx-⦿
    isFunctor.isSetoidHom:map isFunctor:Ctx-⦿ = {!!}
    isFunctor.functoriality-id isFunctor:Ctx-⦿ = {!!}
    isFunctor.functoriality-◆ isFunctor:Ctx-⦿ = {!!}

data Sub-⦿ {K : 𝒰 𝑖} (R : Ctx-⦿ K -> K -> 𝒰 𝑗) (Γ : Ctx-⦿ K) : (Δ : Ctx-⦿ K) -> 𝒰 (𝑖 ､ 𝑗) where
  [] : Sub-⦿ R Γ []
  _,,_ : ∀{Δ k} -> Sub-⦿ R Γ Δ  -> R Γ k -> Sub-⦿ R Γ (Δ ,, k)


