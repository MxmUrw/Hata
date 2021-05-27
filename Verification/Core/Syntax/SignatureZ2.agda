
module Verification.Core.Syntax.SignatureZ2 where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Limit.Kan
-- open import Verification.Unification.RecAccessible


module _ {K : 𝒰₀} where
  -- Symbol : 𝒰₀
  -- Symbol = ∑ λ (n : ℕ) -> K ×-𝒰 (Vec K n)

  ⇈ : (K -> 𝒰₀) -> (K -> 𝒰₀)
  ⇈ V k = Lift 𝟙-𝒰 +-𝒰 V k

  Signature : 𝒰₁
  Signature = {n : ℕ} -> K -> Vec K (suc n) -> 𝒰₀

  isInhabited-Sig : Signature -> 𝒰₀
  isInhabited-Sig σ = ∀ k -> ∑ λ n -> ∑ λ (ks : Vec K (suc n)) -> σ k ks

  data Term (σ : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data Terms (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : Terms σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> Term σ V k -> Terms σ V ks -> Terms σ V (k ∷ ks)

  data Term σ V k where
    te : ∀{ks : Vec K (suc n)} -> σ k ks -> Terms σ V ks -> Term σ V k
    var : V k -> Term σ V k

  module _ {σ : Signature} {V : K -> 𝒰₀} where
    join-Term : {k : K} -> Term σ (Term σ V) k -> Term σ V k

    join-Terms : {ks : Vec K n} -> Terms σ (Term σ V) ks -> Terms σ V ks
    join-Terms [] = []
    join-Terms (t ∷ ts) = join-Term t ∷ join-Terms ts

    join-Term (te t ts) = te t (join-Terms ts)
    join-Term (var x) = x

  module _ (σ : Signature) where
    IdxTerm : IdxSet K ℓ₀ -> IdxSet K ℓ₀
    ⟨ IdxTerm V ⟩ = Term σ ⟨ V ⟩
    of (IdxTerm V) = {!!}

  module _ {σ : Signature} where
    instance
      IdxSet:IdxTerm : {A : K -> 𝒰₀} -> {{_ : IIdxSet K A}} -> IIdxSet K (Term σ A)
      IdxSet:IdxTerm {A} {{_}} = of IdxTerm σ ` A `

  instance
    IdxSet:IdxTerm⇈ : {A : K -> 𝒰₀} -> {{_ : IIdxSet K A}} -> IIdxSet K (⇈ A)
    IdxSet:IdxTerm⇈ {A} = of _+-IdxSet_ 𝟙 ` A `
  -- = #openstruct IdxTerm


  module _ {σ : Signature} {V W : K -> 𝒰₀} where
    map-Term : {k : K} -> (∀{k} -> V k -> W k) -> Term σ V k -> Term σ W k

    map-Terms : {ks : Vec K n} -> (∀{k} -> V k -> W k) -> Terms σ V ks -> Terms σ W ks
    map-Terms f [] = []
    map-Terms f (t ∷ ts) = map-Term f t ∷ map-Terms f ts

    map-Term f (te s ts) = te s (map-Terms f ts)
    map-Term f (var x) = var (f x)

  private
    𝒞 : Category _
    𝒞 = Category:IdxSet K ℓ₀

  module _ (σ : Signature) where
    Functor:Term : Functor 𝒞 𝒞
    ⟨ Functor:Term ⟩ X = IdxTerm σ X
    -- ⟨ ⟨ Functor:Term ⟩ X ⟩ = Term σ ⟨ X ⟩
    -- IIdxSet.ISet:this (of ⟨ Functor:Term ⟩ z) = {!!}
    ⟨ IFunctor.map (of Functor:Term) f ⟩ = map-Term ⟨ f ⟩
    IFunctor.functoriality-id (of Functor:Term) = {!!}
    IFunctor.functoriality-◆ (of Functor:Term) = {!!}
    IFunctor.functoriality-≣ (of Functor:Term) = {!!}

    Monad:Term : Monad 𝒞
    ⟨ Monad:Term ⟩ = Functor:Term
    ⟨ IMonad.return (of Monad:Term) ⟩ x = (var x)
    ⟨ IMonad.join (of Monad:Term) ⟩ = join-Term
    IMonad.INatural:return (of Monad:Term) = {!!}
    IMonad.INatural:join (of Monad:Term) = {!!}
    IMonad.unit-l-join (of Monad:Term) = {!!}
    IMonad.unit-r-join (of Monad:Term) = {!!}
    IMonad.assoc-join (of Monad:Term) = {!!}


    Functor:TermZ2 = Functor:EitherT 𝟙 (Monad:Term)
    Monad:TermZ2 = Monad:EitherT 𝟙 (Monad:Term)

    TermZ2 : (V : K -> 𝒰₀) -> K -> 𝒰₀
    TermZ2 V k = Term σ (⇈ V) k

    IdxTermZ2 : (V : IdxSet K ℓ₀) -> IdxSet K ℓ₀
    IdxTermZ2 V = IdxTerm σ (𝟙 + V)

    TermsZ2 : (V : K -> 𝒰₀) -> (Vec K n) -> 𝒰₀
    TermsZ2 V ks = Terms σ (⇈ V) ks

  module _ {σ : Signature} {V W : IdxSet K ℓ₀} where
    map-TermZ2 : {k : K} -> (V ⟶ W) -> TermZ2 σ ⟨ V ⟩ k -> TermZ2 σ ⟨ W ⟩ k
    map-TermZ2 {k} f = ⟨ map {{of Functor:TermZ2 σ}} f ⟩ {k}

    map-TermsZ2 : {ks : Vec K n} -> (V ⟶ W) -> TermsZ2 σ ⟨ V ⟩ ks -> TermsZ2 σ ⟨ W ⟩ ks
    map-TermsZ2 f = map-Terms (⟨ map-+-r {c = 𝟙} f ⟩ {_})

  module _ {σ : Signature} {V : IdxSet K ℓ₀} where
    join-TermZ2 : {k : K} -> TermZ2 σ (TermZ2 σ ⟨ V ⟩) k -> TermZ2 σ ⟨ V ⟩ k
    join-TermZ2 {k} x = ⟨ join {{of Monad:TermZ2 σ}} {A = V} ⟩ {k} x


