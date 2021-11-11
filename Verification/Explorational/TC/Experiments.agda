
module Verification.Core.Category.TC.Experiments where

open import Verification.Conventions hiding (Square ; extend)
open import Verification.Core.Category.Definition


module Variant1 where
  data Term (A : 𝒰₀) : 𝒰₀ where
    BB NN : Term A
    _⇒_ : Term A -> Term A -> Term A
    var : A -> Term A


  join-Term : ∀{A} -> Term (Term A) -> Term A
  join-Term {A} BB = BB
  join-Term {A} NN = NN
  join-Term {A} (t ⇒ s) = join-Term t ⇒ join-Term s
  join-Term {A} (var t) = t

module Variant2 where
  data Term : (A : 𝒰₀) -> 𝒰₁ where
    BB NN : ∀{A} -> Term A
    _⇒_ : ∀{A} -> Term A -> Term A -> Term A
    var : ∀{A} -> A -> Term A
    ι : ∀{A B} -> (A -> B) -> Term A -> Term B

module Variant3 where
  data Term {A : 𝒰₀} {{_ : ICategory A (ℓ₀ , ℓ₀)}} (F : A -> 𝒰₀) : A -> 𝒰₀ where
    BB NN : ∀{a} -> Term F a
    _⇒_ : ∀{a : A} -> Term F a -> Term F a -> Term F a
    var : ∀{a} -> F a -> Term F a
    -- ι : ∀{a b} -> (a ⟶ b) -> Term F a -> Term F b

  join-Term : ∀{A : 𝒰₀} {{_ : ICategory A (ℓ₀ , ℓ₀)}} (term : A -> A) -> (F : A -> 𝒰₀) -> (∀{a} -> F (term a) ≡-Str Term F a) -> ∀{a} -> Term F (term a) -> Term F a
  join-Term term f _ BB = BB
  join-Term term f _ NN = NN
  join-Term term f P (t ⇒ s) = join-Term term f P t ⇒ join-Term term f P s
  join-Term term F P (var x) = {!!}





module Variant4 where
  data Term {A : 𝒰₀} {{_ : ICategory A (ℓ₀ , ℓ₀)}} (F : A -> 𝒰₀) : A -> 𝒰₀ where
    BB NN : ∀{a} -> Term F a
    _⇒_ : ∀{a : A} -> Term F a -> Term F a -> Term F a
    var : ∀{a} -> F a -> Term F a
    -- ι : ∀{a b} -> (a ⟶ b) -> Term F a -> Term F b

  data Base : 𝒰₀ where
    pt : Base
    term : Base -> Base

  instance
    ICategory:Base : ICategory Base (ℓ₀ , ℓ₀)
    ICategory:Base = {!!}

  {-# NON_TERMINATING #-}
  F : Base -> 𝒰₀
  F pt = 𝟙-𝒰
  F (term b) = Term F b

  join-Term : ∀{a : Base} -> Term F (term a) -> Term F a
  join-Term = {!!}

  -- join-Term : ∀{A : 𝒰₀} {{_ : ICategory A (ℓ₀ , ℓ₀)}} (term : A -> A) -> (F : A -> 𝒰₀) -> (∀{a} -> F (term a) ≡-Str Term F a) -> ∀{a} -> Term F (term a) -> Term F a
  -- join-Term term f _ BB = BB
  -- join-Term term f _ NN = NN
  -- join-Term term f P (t ⇒ s) = join-Term term f P t ⇒ join-Term term f P s
  -- join-Term term F P (var x) = {!!}

module Variant5 where
  postulate T : 𝒰₀ -> 𝒰₀
            A : 𝒰₀
            instance _ : ICategory A (ℓ₀ , ℓ₀)

  data Higher (F : A -> 𝒰₀) : (a : A) -> 𝒰₀ where
    var : ∀{a} -> F a -> Higher F a
    ι : ∀{a b} -> (a ⟶ b) -> Higher F a -> Higher F b
  -- data Term (F : 𝒰₀ -> 𝒰₀) (A : 𝒰₀) : 𝒰₀ where
  --   BB NN : Term A
  --   _⇒_ : Term A -> Term A -> Term A
  --   var : A -> Term A

module Variant6 where
  data Term {A : 𝒰₀} {{_ : ICategory A (ℓ₀ , ℓ₀)}} (F : A -> 𝒰₀) : A -> 𝒰₀ where
    BB NN : ∀{a} -> Term F a
    _⇒_ : ∀{a : A} -> Term F a -> Term F a -> Term F a
    var : ∀{a} -> F a -> Term F a
    ι : ∀{a b} -> (a ⟶ b) -> Term F a -> Term F b

  join-Term : ∀{A : 𝒰₀} {{_ : ICategory A (ℓ₀ , ℓ₀)}}  (F : A -> 𝒰₀) -> ∀{a} -> Term (Term F) a -> Term F a
  join-Term f BB = BB
  join-Term f NN = NN
  join-Term f (t ⇒ s) = join-Term f t ⇒ join-Term f s
  join-Term F (var x) = x
  join-Term F (ι f x) = ι f (join-Term F x)


module Variant7 where
  -- postulate T : 𝒰₀ -> 𝒰₀
  --           A : 𝒰₀
  --           instance _ : ICategory A (ℓ₀ , ℓ₀)
  module _ {K : 𝒰₀} where
    data Higher (T : (K -> 𝒰₀) -> (K -> 𝒰₀)) : (a : K) -> 𝒰₀ where
      var : ∀{a} -> F a -> Higher F a
      -- ι : ∀{a b} -> (a ⟶ b) -> Higher F a -> Higher F b


