
module Verification.Core.Theory.Syndetic.v2.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Definition


data Var (σ : 𝒰₀) (A : 𝒰₀) : 𝒰₀ where
  tok : σ -> Var σ A
  var : A -> Var σ A
  -- nil : Var σ A

record isDirSet (X : Setoid 𝑖) : 𝒰 (𝑖 ⁺) where
  field Dir : 𝒰₀
open isDirSet public

DirSet : ∀ 𝑖 -> 𝒰 _
DirSet 𝑖 = Setoid 𝑖 :& isDirSet

-- record DirSet 𝑖 : 𝒰 𝑖 where
--   ⟨_⟩ : Setoid 𝑖
--   Dir : 𝒰₀
-- open DirSet public

record T∞ (X : DirSet 𝑖) (σ : 𝒰₀) : 𝒰 (𝑖 ⁺) where
  inductive
  field map0 : ⟨ X ⟩ -> (Bool) +-𝒰 ((∑ Var σ) ×-𝒰 (Dir (of X) -> T∞ X σ))
  -- field map1 : ⟨ X ⟩ -> Dir (of X) -> Dir (of X) -> ∑ Var σ

Tree : 𝒰₀
Tree = (List ℕ)

pattern v0 = left false
pattern v1 = left true

instance
  isSetoid:Tree : isSetoid _ Tree
  isSetoid._∼'_ isSetoid:Tree = _≡-Str_
  isSetoid.isEquivRel:∼ isSetoid:Tree = {!!}

instance
  isDirSet:Tree : isDirSet ′ Tree ′
  isDirSet:Tree = record { Dir = Maybe ℕ }

𝕋 : DirSet _
𝕋 = ′ Tree ′

module to-T∞ {σ : Signature} where
  data 𝕍 : 𝒰₀ where
    * : 𝕍
    sig : ∀ {n} -> σ n -> 𝕍

  V = ∑ Var 𝕍
  FF = Maybe ℕ -> T∞ ′ Tree ′ 𝕍
  Zero : T∞ 𝕋 𝕍
  T∞.map0 Zero x = v0

  One : T∞ 𝕋 𝕍
  One = {!!}

  Star : T∞ 𝕋 𝕍
  T∞.map0 Star [] = right ((𝟘-𝒰 , tok *) , either (λ _ -> One) (λ _ -> Zero))
  T∞.map0 Star (x ∷ x₁) = v0
  mutual
    kinded : ∀{n} -> σ n -> FF
    kinded {n} _ nothing = Star
    kinded {n} _ (just x) = <? n x
      where <? : ℕ -> ℕ -> T∞ 𝕋 𝕍
            <? zero zero = Zero
            <? (suc a) zero = Zero
            <? zero (suc b) = Star
            <? (suc a) (suc b) = <? a b

    walks : {A : 𝒰₀} -> ∀{n} -> (ts : Terms σ A n) -> ℕ -> List ℕ -> Bool +-𝒰 ((V) ×-𝒰 FF)
    walks {A} {.0} [] i is = v0
    walks {A} {.(suc _)} (x ∷ ts) zero is = walk x is
    walks {A} {.(suc _)} (x ∷ ts) (suc i) is = walks ts i is

    walk : {A : 𝒰₀} (x : Term σ A) -> (List ℕ) -> Bool +-𝒰 ((V) ×-𝒰 FF)
    walk {A} (te x ts) (i ∷ is) = walks ts i is
    walk {A} (var x) (i ∷ is) = v0
    walk {A} (te s ts) [] = just ((A , tok (sig s)) , kinded s)
    walk {A} (var x) [] = just ((A , var x) , either (λ _ -> Star) (λ _ -> Zero))

  module _ {A : 𝒰₀} (x : Term σ A) where
    -- map0 : Tree -> ∑ Var (∑ σ)
    -- map0 = walk x

    done : T∞ ′ Tree ′ 𝕍
    done = record { map0 = walk x }

{-
-}

{-
data RST {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) : A -> A -> 𝒰 (𝑖 ､ 𝑗) where
  incl : ∀{a b} -> R a b -> RST R a b
  refl-RST : ∀{a} -> RST R a a
  sym-RST : ∀{a b} -> RST R a b -> RST R b a
  trans-RST : ∀{a b c} -> RST R a b -> RST R b c -> RST R a c

data _∼-Tree_ : Tree -> Tree -> 𝒰₀ where
  cancel-Tree : ∀{xs ys : Tree} -> {a : ℕ} -> (xs <> (a ∷ 0 ∷ []) <> ys) ∼-Tree (xs <> ys)
  -- inside-Tree : ∀{xs ys : Tree} -> {a : ℕ} -> (xs <> (a ∷ 0 ∷ []) <> ys) ∼-Tree (xs <> ys)

instance
  isEquivRel:RST : {A : 𝒰 𝑖} {R : A -> A -> 𝒰 𝑗} -> isEquivRel (∼-Base (RST R))
  isEquivRel:RST = {!!}
  -}
